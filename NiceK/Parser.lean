import NiceK.Types
import NiceK.AST
import NiceK.Lexer

/-! ## Parser

Right-to-left, two-level parser for K expressions.

Pipeline: `String → tokenize → List Token → parse → KExpr`

The parser works in two stages:
1. Convert flat token list into `PItem`s (handling parens recursively, grouping
   consecutive ints into vectors, and attaching adverbs to preceding verbs).
2. Parse the item list with two precedence levels:
   - **Term**: a noun optionally preceded by a chain of monadic verbs
     (monadic verbs bind tightly to their immediate right).
   - **Expr**: terms connected by dyadic verbs, right-associative.

Uses fuel-based recursion (`Nat`) — no `partial`, no `!`. -/

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
  | is  =>
    let arr := is.toArray
    .vec arr.size ⟨arr, rfl⟩

/-! ### Stage 2: Two-level precedence parser

**Term**: zero or more monadic verbs followed by a noun.
Monadic verbs bind tightly — `!2+3` parses as `(!2)+3`, not `!(2+3)`.

**Expr**: terms connected by dyadic verbs, right-associative.
`1+2+3` parses as `1+(2+3)`. -/

/-- Parse a term: a chain of monadic verbs applied to a noun.
    Returns `(expr, remaining-items)`. -/
private def parseTerm (fuel : Nat) (items : List PItem) : Except KError (KExpr × List PItem) :=
  match fuel with
  | 0 => .error { kind := .parse, message := "Expression too deeply nested" }
  | fuel + 1 =>
    match items with
    | [] => .error { kind := .parse, message := "Expected expression, got end of input" }
    | .verb v :: rest => do
      let (inner, rest') ← parseTerm fuel rest
      .ok (.monadic v inner, rest')
    | .noun e :: rest => .ok (e, rest)

/-- Parse an expression: a term followed by zero or more `(verb term)` pairs.
    Dyadic application is right-associative. -/
private def parseExpr (fuel : Nat) (items : List PItem) : Except KError KExpr :=
  match fuel with
  | 0 => .error { kind := .parse, message := "Expression too deeply nested" }
  | fuel + 1 => do
    let (left, rest) ← parseTerm fuel items
    match rest with
    | [] => .ok left
    | .verb v :: rest' => do
      let right ← parseExpr fuel rest'
      .ok (.dyadic v left right)
    | .noun _ :: _ =>
      .error { kind := .parse, message := "Two nouns with no verb between them" }

/-! ### Stage 1: Token list → PItem list

We process left-to-right, grouping consecutive int tokens and
handling parentheses recursively by finding the matching `)`.

`fuel` bounds recursion depth (initialized to total token count). -/

/-- Find matching `)` in `tokens`, returning (inner, rest-after-close).
    `depth` starts at 1. Returns `.error` if unmatched. -/
private def findClose (tokens : List Token) (depth : Nat) : Except KError (List Token × List Token) :=
  match tokens with
  | [] => .error { kind := .parse, message := "Unmatched '('" }
  | t :: ts =>
    match t.kind with
    | .lparen => do
      let (inner, rest) ← findClose ts (depth + 1)
      .ok (t :: inner, rest)
    | .rparen =>
      if depth == 1 then .ok ([], ts)
      else do
        let (inner, rest) ← findClose ts (depth - 1)
        .ok (t :: inner, rest)
    | _ => do
      let (inner, rest) ← findClose ts depth
      .ok (t :: inner, rest)

/-- Collect consecutive int tokens, returning (ints, remaining-tokens). -/
private def collectInts : List Token → List Int × List Token
  | { kind := .int i, .. } :: ts =>
    let (more, rest) := collectInts ts
    (i :: more, rest)
  | ts => ([], ts)

/-- Attach any trailing adverb tokens to a verb. -/
private def attachAdverbs (v : KVerb) : List Token → Except KError (KVerb × List Token)
  | { kind := .adverb c, span := sp } :: ts =>
    match charToAdverbSym c with
    | .ok a  => attachAdverbs (.adv a v) ts
    | .error e => .error { e with span := some sp }
  | ts => .ok (v, ts)

/-- Build PItem list from tokens.  `fuel` bounds recursion depth
    (initialized to total token count). -/
private def buildItems (fuel : Nat) (tokens : List Token) : Except KError (List PItem) :=
  match fuel with
  | 0 => match tokens with
    | [] => .ok []
    | _  => .error { kind := .parse, message := "Expression too deeply nested" }
  | fuel + 1 =>
    match tokens with
    | [] => .ok []
    | t :: ts =>
      match t.kind with
      | .int i =>
        let (moreInts, rest) := collectInts ts
        let val := intsToVal (i :: moreInts)
        do let items ← buildItems fuel rest
           .ok (.noun (.val val) :: items)
      | .verb c => do
        let sym ← charToVerbSym c
        let v := KVerb.prim sym
        let (v', rest) ← attachAdverbs v ts
        let items ← buildItems fuel rest
        .ok (.verb v' :: items)
      | .adverb _ =>
        .error { kind := .parse, message := "Adverb must follow a verb", span := some t.span }
      | .lparen => do
        let (inner, rest) ← findClose ts 1
        let innerItems ← buildItems fuel inner
        let innerExpr ← parseExpr (innerItems.length + 1) innerItems
        let items ← buildItems fuel rest
        .ok (.noun innerExpr :: items)
      | .rparen =>
        .error { kind := .parse, message := "Unmatched ')'", span := some t.span }
      | .ident name => do
        let items ← buildItems fuel ts
        .ok (.noun (.var name) :: items)

/-! ### Top-level API -/

def parse (s : String) : Except KError KExpr := do
  let tokens ← tokenize s
  let fuel := tokens.length + 1
  let items ← buildItems fuel tokens
  parseExpr (items.length + 1) items
