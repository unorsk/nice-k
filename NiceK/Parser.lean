import NiceK.Types
import NiceK.AST
import NiceK.Lexer

/-! ## Parser

Right-to-left, two-level parser for K expressions.

Pipeline: `String → tokenize → List Token → parse → KExpr`

The parser works in two stages:
1. Convert flat token list into `PItem`s using a single-pass stack + phase
   machine (handling parens/braces/brackets via a frame stack, grouping
   consecutive ints, and attaching adverbs to preceding verbs).
   Terminates by `(tokens.length, phase.rank)` — same pattern as the lexer.
2. Parse the item list with two precedence levels:
   - **Term**: a noun optionally preceded by a chain of monadic verbs
     (monadic verbs bind tightly to their immediate right).
   - **Expr**: terms connected by dyadic verbs, right-associative.

No `partial`, no fuel. -/

/-- A parsed item: either a noun (expression) or a verb. -/
inductive PItem where
  | noun   : KExpr → PItem
  | verb   : KVerb → PItem
  | assign : PItem
  | semi   : PItem

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
private def verbAsValue (v : KVerb) : KExpr :=
  .val (.fn (.primVerb v))

private def parseTerm (items : List PItem)
    : Except KError (KExpr × { rest : List PItem // rest.length < items.length }) :=
  match items with
  | [] => .error { kind := .parse, message := "Expected expression, got end of input" }
  | .verb v :: [] =>
    .ok (verbAsValue v, ⟨[], by simp [List.length_cons]⟩)
  | .verb v :: (.semi :: tail) =>
    .ok (verbAsValue v, ⟨.semi :: tail, by simp [List.length_cons]⟩)
  | .verb v :: (.assign :: tail) =>
    .ok (verbAsValue v, ⟨.assign :: tail, by simp [List.length_cons]⟩)
  | .verb v :: rest => do
    let (inner, ⟨rest', h⟩) ← parseTerm rest
    .ok (.monadic v inner, ⟨rest', by simp [List.length_cons]; omega⟩)
  | .noun e :: rest => .ok (e, ⟨rest, by simp [List.length_cons]⟩)
  | .assign :: _ => .error { kind := .syntax, message := "Unexpected ':' at start of expression" }
  | .semi :: _ => .error { kind := .syntax, message := "Unexpected ';' at start of expression" }

/-- Parse the tail of an expression: zero or more `(verb term)` pairs,
    right-associative.  Terminates by `rest.length`. -/
private def parseTail (left : KExpr) (rest : List PItem)
    : Except KError (KExpr × List PItem) :=
  match h : rest with
  | [] => .ok (left, [])
  | .semi :: _ => .ok (left, rest)   -- stop; semicolons handled by parseProgram
  | .assign :: rest' =>
    match parseTerm rest' with
    | .error e => .error e
    | .ok (nextTerm, ⟨rest'', _⟩) =>
      have : rest''.length < rest.length := by rw [h]; simp [List.length_cons]; omega
      match parseTail nextTerm rest'' with
      | .error e => .error e
      | .ok (rhs, remaining) =>
        match left with
        | .var name => .ok (.assign name rhs, remaining)
        | _ => .error { kind := .syntax,
                        message := "Left side of ':' must be a variable name" }
  | .verb v :: rest' =>
    match parseTerm rest' with
    | .error e => .error e
    | .ok (nextTerm, ⟨rest'', _⟩) =>
      have : rest''.length < rest.length := by rw [h]; simp [List.length_cons]; omega
      match parseTail nextTerm rest'' with
      | .error e => .error e
      | .ok (rightExpr, remaining) => .ok (.dyadic v left rightExpr, remaining)
  | .noun _ :: _ =>
    .error { kind := .parse, message := "Two nouns with no verb between them" }
termination_by rest.length

/-- Parse a single expression (no semicolons). Returns parsed expr and remaining items. -/
private def parseExpr (items : List PItem) : Except KError (KExpr × List PItem) :=
  match parseTerm items with
  | .error e => .error e
  | .ok (left, ⟨rest, _⟩) => parseTail left rest

/-- Parse a program: one or more expressions separated by `;`, left-to-right sequencing.
    Uses `partial` since proving that parseExpr strictly shrinks the item list
    requires threading subtype proofs through parseTail — acceptable for now. -/
private partial def parseProgram (items : List PItem) : Except KError KExpr := do
  let (first, rest) ← parseExpr items
  let rec go (acc : KExpr) (remaining : List PItem) : Except KError KExpr :=
    match remaining with
    | [] => .ok acc
    | .semi :: rest' =>
      if rest'.isEmpty then
        .error { kind := .syntax, message := "Trailing ';' — empty expression after semicolon" }
      else do
        let (expr, rest'') ← parseExpr rest'
        go (.seq acc expr) rest''
    | _ => .error { kind := .parse, message := "Unexpected items after expression" }
  go first rest

/-- Parse a semicolon-separated argument list from PItems. -/
private partial def parseArgs (items : List PItem) : Except KError (List KExpr) := do
  if items.isEmpty then return []
  let (e, rest) ← parseExpr items
  match rest with
  | [] => return [e]
  | .semi :: rest' => do
    let more ← parseArgs rest'
    return e :: more
  | _ => .error { kind := .parse, message := "Unexpected item in argument list" }

/-- Extract parameter names from bracket-params items.
    Expected form: ident;ident;... or empty. -/
private def parseParamNames : List PItem → Except KError (List String)
  | [] => .ok []
  | [.noun (.var name)] => .ok [name]
  | .noun (.var name) :: .semi :: rest => do
    let more ← parseParamNames rest
    .ok (name :: more)
  | _ => .error { kind := .syntax,
                  message := "Invalid parameter list — expected variable names separated by ';'" }

/-! ### Implicit parameter arity inference

Scans a `KExpr` for uses of `x`, `y`, `z` (the implicit parameters).
Does **not** recurse into nested lambdas, since those have their own scope. -/

private def implicitArity : KExpr → Nat
  | .var "x"          => 1
  | .var "y"          => 2
  | .var "z"          => 3
  | .lam _ _          => 0   -- stop at nested lambda
  | .app f as         => max (implicitArity f) (as.foldl (fun m a => max m (implicitArity a)) 0)
  | .monadic _ e      => implicitArity e
  | .dyadic _ l r     => max (implicitArity l) (implicitArity r)
  | .assign _ rhs     => implicitArity rhs
  | .seq a b          => max (implicitArity a) (implicitArity b)
  | _                 => 0

/-! ### Stage 1: Token list → PItem list (single-pass stack + phase machine)

We process left-to-right, consuming one token per step (or flushing the
current phase with no token consumed but decreasing phase rank).

A **frame stack** tracks nested delimiters (parens, braces, brackets).
Each frame accumulates `PItem`s in reverse order.  On the closing
delimiter the innermost frame is closed and its items are processed
according to the frame kind.

A **max nesting depth** guards against pathological inputs and produces
a friendly error pointing at the delimiter that exceeded the limit. -/

/-- The kind of a frame: determines how its contents are processed on close. -/
private inductive FrameKind where
  | root
  | paren
  | brace (params : Option (List String))   -- lambda body; params set when [..] is parsed
  | bracketApp (callee : KExpr)             -- f[args]; callee popped from parent
  | bracketParams                           -- parameter list inside {[...] ...}

/-- A delimiter frame: items accumulated so far (in reverse) and the
    span of the opening delimiter (none for the root). -/
private structure Frame where
  itemsRev : List PItem
  openSpan : Option SourceSpan
  kind     : FrameKind

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

/-- Check that all delimiters are closed at end of input. -/
private def finalizeEOF (stk : List Frame) : Except KError (List Frame) :=
  match stk with
  | [root] => .ok [root]
  | f :: _ =>
    let msg := match f.kind with
      | .paren => "Unmatched '('"
      | .brace _ => "Unmatched '{'"
      | .bracketApp _ => "Unmatched '['"
      | .bracketParams => "Unmatched '[' in parameter list"
      | .root => "internal: multiple root frames"
    .error { kind := .parse, message := msg, span := f.openSpan }
  | [] => .error { kind := .parse, message := "internal: empty frame stack" }

/-- Close a paren frame on `)`. -/
private def closeParenFrame (rparenSpan : SourceSpan) (stk : List Frame)
    : Except KError (List Frame) := do
  match stk with
  | [] => .error { kind := .parse, message := "internal: empty frame stack" }
  | inner :: parent :: rest =>
    match inner.kind with
    | .paren => do
      let innerItems := inner.itemsRev.reverse
      let innerExpr ← parseProgram innerItems
        |>.mapError (·.withContext "while parsing parenthesized expression")
      let parent' := { parent with itemsRev := (.noun innerExpr) :: parent.itemsRev }
      .ok (parent' :: rest)
    | _ => .error { kind := .parse, message := "Mismatched ')' — expected a different closing delimiter",
                    span := some rparenSpan }
  | [_root] =>
    .error { kind := .parse, message := "Unmatched ')'", span := some rparenSpan }

/-- Close a brace frame on `}`, producing a lambda. -/
private def closeBraceFrame (rbraceSpan : SourceSpan) (stk : List Frame)
    : Except KError (List Frame) := do
  match stk with
  | [] => .error { kind := .parse, message := "internal: empty frame stack" }
  | inner :: parent :: rest =>
    match inner.kind with
    | .brace declaredParams => do
      let bodyItems := inner.itemsRev.reverse
      let body ← if bodyItems.isEmpty then
        .ok (.val (.atom 0))  -- empty body returns 0 (K convention: :: but we use 0)
      else
        parseProgram bodyItems
          |>.mapError (·.withContext "while parsing lambda body")
      let paramSpec := match declaredParams with
        | some names => ParamSpec.explicit names
        | none       => ParamSpec.implicit
      let parent' := { parent with itemsRev := (.noun (.lam paramSpec body)) :: parent.itemsRev }
      .ok (parent' :: rest)
    | _ => .error { kind := .parse, message := "Mismatched '}' — expected a different closing delimiter",
                    span := some rbraceSpan }
  | [_root] =>
    .error { kind := .parse, message := "Unmatched '}'", span := some rbraceSpan }

/-- Close a bracket-app frame on `]`, producing an application. -/
private def closeBracketApp (rbrackSpan : SourceSpan) (stk : List Frame)
    : Except KError (List Frame) := do
  match stk with
  | [] => .error { kind := .parse, message := "internal: empty frame stack" }
  | inner :: parent :: rest =>
    match inner.kind with
    | .bracketApp callee => do
      let argItems := inner.itemsRev.reverse
      let args ← parseArgs argItems
        |>.mapError (·.withContext "while parsing function arguments")
      let parent' := { parent with itemsRev := (.noun (.app callee args)) :: parent.itemsRev }
      .ok (parent' :: rest)
    | _ => .error { kind := .parse, message := "Mismatched ']'",
                    span := some rbrackSpan }
  | [_root] =>
    .error { kind := .parse, message := "Unmatched ']'", span := some rbrackSpan }

/-- Close a bracket-params frame on `]`, storing params in the parent brace frame. -/
private def closeBracketParams (rbrackSpan : SourceSpan) (stk : List Frame)
    : Except KError (List Frame) := do
  match stk with
  | [] => .error { kind := .parse, message := "internal: empty frame stack" }
  | inner :: braceFrame :: rest =>
    match inner.kind, braceFrame.kind with
    | .bracketParams, .brace _ => do
      let paramItems := inner.itemsRev.reverse
      let paramNames ← parseParamNames paramItems
        |>.mapError (·.withContext "while parsing lambda parameters")
      let braceFrame' := { braceFrame with kind := .brace (some paramNames) }
      .ok (braceFrame' :: rest)
    | _, _ => .error { kind := .parse,
                       message := "internal: bracket-params frame not inside a brace frame",
                       span := some rbrackSpan }
  | [_] => .error { kind := .parse, message := "Unmatched ']'", span := some rbrackSpan }

/-- Maximum allowed nesting depth. -/
def maxNestingDepth : Nat := 256

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
        if depth + 1 > maxNestingDepth then
          .error { kind := .parse
                 , message := s!"Maximum nesting depth exceeded ({maxNestingDepth})"
                 , span := some t.span }
        else
          let newFrame : Frame := { itemsRev := [], openSpan := some t.span, kind := .paren }
          buildItemsCore .ready (newFrame :: stk) ts
      | .rparen => do
        let stk' ← closeParenFrame t.span stk
        buildItemsCore .ready stk' ts
      | .lbrace =>
        let depth := stk.length - 1
        if depth + 1 > maxNestingDepth then
          .error { kind := .parse
                 , message := s!"Maximum nesting depth exceeded ({maxNestingDepth})"
                 , span := some t.span }
        else
          let newFrame : Frame := { itemsRev := [], openSpan := some t.span, kind := .brace none }
          buildItemsCore .ready (newFrame :: stk) ts
      | .rbrace => do
        let stk' ← closeBraceFrame t.span stk
        buildItemsCore .ready stk' ts
      | .lbrack =>
        match stk with
        | [] => .error { kind := .parse, message := "internal: empty frame stack" }
        | topFrame :: restFrames =>
          match topFrame.kind with
          -- Inside a brace frame with no items yet → parameter list
          | .brace none =>
            if topFrame.itemsRev.isEmpty then
              let paramFrame : Frame := { itemsRev := [], openSpan := some t.span, kind := .bracketParams }
              buildItemsCore .ready (paramFrame :: topFrame :: restFrames) ts
            else
              -- [ inside brace body after some items: check if last item is a noun for app
              match topFrame.itemsRev with
              | .noun callee :: parentRest =>
                let topFrame' := { topFrame with itemsRev := parentRest }
                let appFrame : Frame := { itemsRev := [], openSpan := some t.span, kind := .bracketApp callee }
                buildItemsCore .ready (appFrame :: topFrame' :: restFrames) ts
              | _ => .error { kind := .syntax,
                              message := "Unexpected '[' — must follow a value or function",
                              span := some t.span }
          -- Elsewhere: application brackets (must follow a noun)
          | _ =>
            match topFrame.itemsRev with
            | .noun callee :: parentRest =>
              let topFrame' := { topFrame with itemsRev := parentRest }
              let appFrame : Frame := { itemsRev := [], openSpan := some t.span, kind := .bracketApp callee }
              buildItemsCore .ready (appFrame :: topFrame' :: restFrames) ts
            | _ => .error { kind := .syntax,
                            message := "Unexpected '[' — must follow a value or function",
                            span := some t.span }
      | .rbrack =>
        match stk with
        | [] => .error { kind := .parse, message := "internal: empty frame stack" }
        | topFrame :: _ =>
          match topFrame.kind with
          | .bracketApp _ => do
            let stk' ← closeBracketApp t.span stk
            buildItemsCore .ready stk' ts
          | .bracketParams => do
            let stk' ← closeBracketParams t.span stk
            buildItemsCore .ready stk' ts
          | _ => .error { kind := .parse,
                          message := "Unmatched ']'",
                          span := some t.span }
      | .colon => do
        let stk' ← pushItem .assign stk
        buildItemsCore .ready stk' ts
      | .semi => do
        let stk' ← pushItem .semi stk
        buildItemsCore .ready stk' ts
termination_by (tokens.length, ph.rank)
decreasing_by all_goals simp [BuildPhase.rank]; omega

/-- Build PItem list from tokens. -/
private def buildItems (tokens : List Token) : Except KError (List PItem) := do
  let root : Frame := { itemsRev := [], openSpan := none, kind := .root }
  let stk ← buildItemsCore .ready [root] tokens
  match stk with
  | [root] => .ok root.itemsRev.reverse
  | _ => .error { kind := .parse, message := "internal: stack not empty at end" }

/-! ### Top-level API -/

def parse (s : String) : Except KError KExpr := do
  let tokens ← tokenize s
  let items ← buildItems tokens
  parseProgram items
