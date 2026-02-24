import NiceK.Types

/-! ## Lexer

Tokenizes a K source string into a list of tokens with source spans.
Single-function state machine with lexicographic termination on
`(chars.length, phase.rank)` — no `partial`, no `!`. -/

inductive TokenKind where
  | int    : Int → TokenKind
  | verb   : Char → TokenKind
  | adverb : Char → TokenKind
  | lparen : TokenKind
  | rparen : TokenKind
  | ident  : String → TokenKind
deriving BEq, Inhabited

def TokenKind.toString : TokenKind → String
  | .int i     => s!"int({i})"
  | .verb c    => s!"verb({c})"
  | .adverb c  => s!"adverb({c})"
  | .lparen    => "("
  | .rparen    => ")"
  | .ident s   => s!"ident({s})"

instance : ToString TokenKind := ⟨TokenKind.toString⟩

structure Token where
  kind : TokenKind
  span : SourceSpan
deriving Inhabited

instance : ToString Token := ⟨fun t => s!"{t.kind}@{t.span}"⟩

def isVerbChar (c : Char) : Bool :=
  c == '+' || c == '!' || c == '#'

def isAdverbChar (c : Char) : Bool :=
  c == '\''

/-- Lexer phase: either ready to start a new token, or accumulating
    a multi-character token (digits or identifier). -/
inductive LexPhase where
  | ready
  | digits (startPos : Nat) (acc : List Char) (neg : Bool)
  | ident  (startPos : Nat) (acc : List Char)

def LexPhase.rank : LexPhase → Nat
  | .ready    => 0
  | .digits _ _ _ => 1
  | .ident _ _    => 1

private def digitsToNat (digits : List Char) : Nat :=
  digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

private def mkIntToken (startPos endPos : Nat) (acc : List Char) (neg : Bool) : Token :=
  let n := digitsToNat acc.reverse
  let v : Int := if neg then -(n : Int) else (n : Int)
  { kind := .int v, span := ⟨startPos, endPos⟩ }

private def mkIdentToken (startPos endPos : Nat) (acc : List Char) : Token :=
  { kind := .ident (String.ofList acc.reverse), span := ⟨startPos, endPos⟩ }

/-- Core lexer.  Termination by `(chars.length, phase.rank)`:
    - In `ready`, we always consume a char → length decreases.
    - In `digits`/`ident` with matching char, we consume → length decreases.
    - In `digits`/`ident` with non-matching char, we switch to `ready`
      on the same list → length same, rank decreases (1→0). -/
def lexCore (phase : LexPhase) (chars : List Char) (pos : Nat)
    : Except KError (List Token) :=
  match phase, chars with
  -- End of input
  | .ready, [] => .ok []
  | .digits sp acc neg, [] => .ok [mkIntToken sp pos acc neg]
  | .ident sp acc, [] => .ok [mkIdentToken sp pos acc]

  -- Accumulating digits
  | .digits sp acc neg, c :: cs =>
    if c.isDigit then
      lexCore (.digits sp (c :: acc) neg) cs (pos + 1)
    else
      -- Flush the number token, re-dispatch current char
      let tok := mkIntToken sp pos acc neg
      do let rest ← lexCore .ready (c :: cs) pos
         .ok (tok :: rest)

  -- Accumulating identifier
  | .ident sp acc, c :: cs =>
    if c.isAlphanum || c == '_' then
      lexCore (.ident sp (c :: acc)) cs (pos + 1)
    else
      let tok := mkIdentToken sp pos acc
      do let rest ← lexCore .ready (c :: cs) pos
         .ok (tok :: rest)

  -- Ready: dispatch on current character
  | .ready, c :: cs =>
    if c == ' ' || c == '\t' || c == '\n' then
      lexCore .ready cs (pos + 1)
    else if c == '(' then
      do let rest ← lexCore .ready cs (pos + 1)
         .ok ({ kind := .lparen, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == ')' then
      do let rest ← lexCore .ready cs (pos + 1)
         .ok ({ kind := .rparen, span := ⟨pos, pos + 1⟩ } :: rest)
    else if isAdverbChar c then
      do let rest ← lexCore .ready cs (pos + 1)
         .ok ({ kind := .adverb c, span := ⟨pos, pos + 1⟩ } :: rest)
    else if isVerbChar c then
      do let rest ← lexCore .ready cs (pos + 1)
         .ok ({ kind := .verb c, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == '-' then
      -- Peek: if next char is a digit, start negative literal
      match cs.head? with
      | some d =>
        if d.isDigit then
          -- Enter digits phase for negative number; consume '-' only,
          -- the digit will be consumed on next iteration in .digits phase.
          lexCore (.digits pos [] true) cs (pos + 1)
        else
          do let rest ← lexCore .ready cs (pos + 1)
             .ok ({ kind := .verb '-', span := ⟨pos, pos + 1⟩ } :: rest)
      | none =>
        .ok [{ kind := .verb '-', span := ⟨pos, pos + 1⟩ }]
    else if c.isDigit then
      lexCore (.digits pos [c] false) cs (pos + 1)
    else if c.isAlpha || c == '_' then
      lexCore (.ident pos [c]) cs (pos + 1)
    else
      .error { kind := .parse, message := s!"Unexpected character '{c}'",
               span := some ⟨pos, pos + 1⟩ }
termination_by (chars.length, phase.rank)
decreasing_by all_goals simp [LexPhase.rank]; omega

def tokenize (s : String) : Except KError (List Token) :=
  lexCore .ready s.toList 0
