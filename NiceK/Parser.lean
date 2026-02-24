import NiceK.Types
import NiceK.AST
import NiceK.Lexer

/-! ## Parser

Right-to-left reducer for K expressions.

Pipeline: `String → tokenize → List Token → parse → KExpr`

The parser works in two stages:
1. Convert flat token list into `PItem`s (handling parens recursively, grouping
   consecutive ints into vectors, and attaching adverbs to preceding verbs).
2. Reduce the item list right-to-left into a `KExpr`, deciding monadic vs
   dyadic based on context.

Uses fuel-based recursion (`Nat`) — no `partial`, no `!`. -/

/-- A parsed item: either a noun (expression) or a verb. -/
inductive PItem where
  | noun : KExpr → PItem
  | verb : KVerb → PItem

private def charToVerbSym (c : Char) : Except KError VerbSym :=
  match c with
  | '+' => .ok .plus
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

/-! ### Stage 2: Right-to-left reduction

Given `[item₁, item₂, ..., itemₙ]`, we reverse and fold:
- A **noun** at the rightmost position becomes the initial expression.
- A **verb** followed (to its right) by an expression with no noun
  to its left → **monadic** application.
- A **noun** to the left of a verb → **dyadic** application. -/

/-- Reduce a reversed item list (rightmost-first) into a KExpr.
    `acc` is the expression built so far (from the right). -/
private def reduceRev : List PItem → Option KExpr → Except KError KExpr
  | [], some acc => .ok acc
  | [], none     => .error { kind := .parse, message := "Empty expression" }
  | .noun e :: rest, none => reduceRev rest (some e)
  | .noun _ :: _, some _ =>
    .error { kind := .parse, message := "Two nouns with no verb between them" }
  | .verb v :: .noun left :: rest, some acc =>
    reduceRev rest (some (.dyadic v left acc))
  | .verb v :: rest, some acc =>
    reduceRev rest (some (.monadic v acc))
  | .verb v :: _, none =>
    .error { kind := .parse, message := s!"Verb '{v}' with no argument to its right" }

private def reduceItems (items : List PItem) : Except KError KExpr :=
  reduceRev items.reverse none

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
private def attachAdverbs (v : KVerb) : List Token → KVerb × List Token
  | { kind := .adverb c, .. } :: ts =>
    match charToAdverbSym c with
    | .ok a  => attachAdverbs (.adv a v) ts
    | .error _ => (v, { kind := .adverb c, span := ⟨0,0⟩ } :: ts)
  | ts => (v, ts)

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
        let (v', rest) := attachAdverbs v ts
        let items ← buildItems fuel rest
        .ok (.verb v' :: items)
      | .adverb _ =>
        .error { kind := .parse, message := "Adverb must follow a verb", span := some t.span }
      | .lparen => do
        let (inner, rest) ← findClose ts 1
        let innerItems ← buildItems fuel inner
        let innerExpr ← reduceItems innerItems
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
  reduceItems items
