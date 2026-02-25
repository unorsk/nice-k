import NiceK.Types
import NiceK.AST
import NiceK.Lexer

/-! ## Parser

Right-to-left, two-level parser for K expressions.

Pipeline: `String → tokenize → List Token → parse → KExpr`

The parser works in two stages:
1. Convert flat token list into `PItem`s using a single-pass stack + phase
   machine (handling parens via a frame stack, grouping consecutive ints,
   and attaching adverbs to preceding verbs).  Terminates by
   `(tokens.length, phase.rank)` — same pattern as the lexer.
2. Parse the item list with two precedence levels:
   - **Term**: a noun optionally preceded by a chain of monadic verbs
     (monadic verbs bind tightly to their immediate right).
   - **Expr**: terms connected by dyadic verbs, right-associative.

No `partial`, no fuel. -/

/-- A parsed item: either a noun (expression) or a verb. -/
inductive PItem where
  | noun : KExpr → PItem
  | verb : KVerb → PItem

private def charToVerbSym (c : Char) : Except KError VerbSym :=
  match c with
  | '+' => .ok .plus
  | '-' => .ok .minus
  | '!' => .ok .bang
  | '#' => .ok .hash
  | _   => .error { kind := .parse, message := s!"Unknown verb symbol '{c}'" }

private def charToAdverbSym (c : Char) : Except KError AdverbSym :=
  match c with
  | '\'' => .ok .each
  | _    => .error { kind := .parse, message := s!"Unknown adverb symbol '{c}'" }

/-- Convert a non-empty list of integers to a KVal. -/
private def intsToVal : List Int → KVal
  | [i] => .atom i
  | is  => .vec is.toArray

/-! ### Stage 2: Two-level precedence parser

**Term**: zero or more monadic verbs followed by a noun.
Monadic verbs bind tightly — `!2+3` parses as `(!2)+3`, not `!(2+3)`.

**Expr**: terms connected by dyadic verbs, right-associative.
`1+2+3` parses as `1+(2+3)`. -/

/-- Parse a term: a chain of monadic verbs applied to a noun.
    Returns `(expr, remaining-items)` with proof the remainder is shorter.
    Structurally recursive on the item list. -/
private def parseTerm (items : List PItem)
    : Except KError (KExpr × { rest : List PItem // rest.length < items.length }) :=
  match items with
  | [] => .error { kind := .parse, message := "Expected expression, got end of input" }
  | .verb v :: rest => do
    let (inner, ⟨rest', h⟩) ← parseTerm rest
    .ok (.monadic v inner, ⟨rest', by simp [List.length_cons]; omega⟩)
  | .noun e :: rest => .ok (e, ⟨rest, by simp [List.length_cons]⟩)

/-- Parse the tail of an expression: zero or more `(verb term)` pairs,
    right-associative.  Terminates by `rest.length`. -/
private def parseTail (left : KExpr) (rest : List PItem) : Except KError KExpr :=
  match h : rest with
  | [] => .ok left
  | .verb v :: rest' =>
    match parseTerm rest' with
    | .error e => .error e
    | .ok (nextTerm, ⟨rest'', _⟩) =>
      have : rest''.length < rest.length := by rw [h]; simp [List.length_cons]; omega
      match parseTail nextTerm rest'' with
      | .error e => .error e
      | .ok rightExpr => .ok (.dyadic v left rightExpr)
  | .noun _ :: _ =>
    .error { kind := .parse, message := "Two nouns with no verb between them" }
termination_by rest.length

/-- Parse an expression: a term followed by zero or more `(verb term)` pairs.
    Dyadic application is right-associative. -/
private def parseExpr (items : List PItem) : Except KError KExpr :=
  match parseTerm items with
  | .error e => .error e
  | .ok (left, ⟨rest, _⟩) => parseTail left rest

/-! ### Stage 1: Token list → PItem list (single-pass stack + phase machine)

We process left-to-right, consuming one token per step (or flushing the
current phase with no token consumed but decreasing phase rank).

A **frame stack** tracks nested parentheses.  Each frame accumulates
`PItem`s in reverse order.  On `)` the innermost frame is closed by
parsing its items into a `KExpr` and pushing it as a noun into the
parent frame.

A **max nesting depth** guards against pathological inputs and produces
a friendly error pointing at the `(` that exceeded the limit. -/

/-- A parenthesis frame: items accumulated so far (in reverse) and the
    span of the `(` that opened this frame (none for the root). -/
private structure Frame where
  itemsRev : List PItem
  openSpan : Option SourceSpan

/-- Phase of the item builder (mirrors the lexer's phase pattern). -/
private inductive BuildPhase where
  | ready
  | ints (firstSpan : SourceSpan) (accRev : List Int)
  | verb (v : KVerb) (vSpan : SourceSpan)

private def BuildPhase.rank : BuildPhase → Nat
  | .ready    => 0
  | .ints ..  => 1
  | .verb ..  => 1

/-- Push an item into the topmost frame. -/
private def pushItem (it : PItem) : List Frame → Except KError (List Frame)
  | [] => .error { kind := .parse, message := "internal: empty frame stack" }
  | f :: fs => .ok ({ f with itemsRev := it :: f.itemsRev } :: fs)

/-- Flush any pending phase into the frame stack (non-recursive helper). -/
private def flushPhaseToStack (ph : BuildPhase) (stk : List Frame)
    : Except KError (List Frame) :=
  match ph with
  | .ready => .ok stk
  | .ints _ accRev => pushItem (.noun (.val (intsToVal accRev.reverse))) stk
  | .verb v _ => pushItem (.verb v) stk

/-- Check that all parentheses are closed at end of input. -/
private def finalizeEOF (stk : List Frame) : Except KError (List Frame) :=
  match stk with
  | [root] => .ok [root]
  | f :: _ => .error { kind := .parse, message := "Unmatched '('", span := f.openSpan }
  | [] => .error { kind := .parse, message := "internal: empty frame stack" }

/-- Close the innermost frame on `)`, parsing its items into a `KExpr`
    and pushing the result as a noun into the parent frame. -/
private def closeFrame (rparenSpan : SourceSpan) (stk : List Frame)
    : Except KError (List Frame) := do
  match stk with
  | [] => .error { kind := .parse, message := "internal: empty frame stack" }
  | [_root] =>
    .error { kind := .parse, message := "Unmatched ')'", span := some rparenSpan }
  | inner :: parent :: rest => do
    let innerItems := inner.itemsRev.reverse
    let innerExpr ← parseExpr innerItems
      |>.mapError (·.withContext "while parsing parenthesized expression")
    let parent' := { parent with itemsRev := (.noun innerExpr) :: parent.itemsRev }
    .ok (parent' :: rest)

/-- Maximum allowed parenthesis nesting depth. -/
def maxParenDepth : Nat := 256

/-- Core single-pass item builder.  Termination by `(tokens.length, phase.rank)`:
    - In `ready`, we always consume a token → length decreases.
    - In `ints`/`verb` with matching token, we consume → length decreases.
    - In `ints`/`verb` with non-matching token, we flush inline to `ready`
      on the same token list → length same, rank decreases (1→0). -/
private def buildItemsCore (ph : BuildPhase) (stk : List Frame) (tokens : List Token)
    : Except KError (List Frame) :=
  match tokens with
  | [] => do
    let stk' ← flushPhaseToStack ph stk
    finalizeEOF stk'
  | t :: ts =>
    match ph with
    -- Accumulating consecutive ints
    | .ints firstSpan accRev =>
      match t.kind with
      | .int i => buildItemsCore (.ints firstSpan (i :: accRev)) stk ts
      | _ => do
        -- Flush ints, re-dispatch current token in ready (rank 1→0)
        let stk' ← pushItem (.noun (.val (intsToVal accRev.reverse))) stk
        buildItemsCore .ready stk' (t :: ts)
    -- Accumulating adverbs onto a verb
    | .verb v vSpan =>
      match t.kind with
      | .adverb c =>
        match charToAdverbSym c with
        | .ok a  => buildItemsCore (.verb (.adv a v) vSpan) stk ts
        | .error e => .error { e with span := some t.span }
      | _ => do
        -- Flush verb, re-dispatch current token in ready (rank 1→0)
        let stk' ← pushItem (.verb v) stk
        buildItemsCore .ready stk' (t :: ts)
    -- Ready: dispatch on current token kind
    | .ready =>
      match t.kind with
      | .int i =>
        buildItemsCore (.ints t.span [i]) stk ts
      | .verb c =>
        match charToVerbSym c with
        | .ok sym => buildItemsCore (.verb (.prim sym) t.span) stk ts
        | .error e => .error { e with span := some t.span }
      | .adverb _ =>
        .error { kind := .parse, message := "Adverb must follow a verb", span := some t.span }
      | .ident name => do
        let stk' ← pushItem (.noun (.var name)) stk
        buildItemsCore .ready stk' ts
      | .lparen =>
        let depth := stk.length - 1
        if depth + 1 > maxParenDepth then
          .error { kind := .parse
                 , message := s!"Maximum nesting depth exceeded ({maxParenDepth})"
                 , span := some t.span }
        else
          let newFrame : Frame := { itemsRev := [], openSpan := some t.span }
          buildItemsCore .ready (newFrame :: stk) ts
      | .rparen => do
        let stk' ← closeFrame t.span stk
        buildItemsCore .ready stk' ts
termination_by (tokens.length, ph.rank)
decreasing_by all_goals simp [BuildPhase.rank]; omega

/-- Build PItem list from tokens. -/
private def buildItems (tokens : List Token) : Except KError (List PItem) := do
  let root : Frame := { itemsRev := [], openSpan := none }
  let stk ← buildItemsCore .ready [root] tokens
  match stk with
  | [root] => .ok root.itemsRev.reverse
  | _ => .error { kind := .parse, message := "internal: stack not empty at end" }

/-! ### Top-level API -/

def parse (s : String) : Except KError KExpr := do
  let tokens ← tokenize s
  let items ← buildItems tokens
  parseExpr items
