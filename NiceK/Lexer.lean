import NiceK.Types

/-! ## Lexer

Tokenizes a K source string into a list of tokens with source spans.
Single-function state machine with lexicographic termination on
`(chars.length, phase.rank)` — no `partial`, no `!`.

The `nctx` ("negative context") flag controls whether `-` followed by
a digit starts a negative literal or is the subtract verb:
  - `true`  at start of input, after whitespace, `(`, a verb, or an adverb
  - `false` after a noun (int, ident, `)`)
This gives correct behaviour for `1-2` (subtract) vs `1 -2` (vector). -/

inductive TokenKind where
  | int    : Int → TokenKind
  | verb   : Char → TokenKind
  | adverb : Char → TokenKind
  | lparen : TokenKind
  | rparen : TokenKind
  | lbrace : TokenKind
  | rbrace : TokenKind
  | lbrack : TokenKind
  | rbrack : TokenKind
  | ident  : String → TokenKind
  | colon  : TokenKind
  | semi   : TokenKind
deriving BEq, Inhabited

def TokenKind.toString : TokenKind → String
  | .int i     => s!"int({i})"
  | .verb c    => s!"verb({c})"
  | .adverb c  => s!"adverb({c})"
  | .lparen    => "("
  | .rparen    => ")"
  | .lbrace    => "{"
  | .rbrace    => "}"
  | .lbrack    => "["
  | .rbrack    => "]"
  | .ident s   => s!"ident({s})"
  | .colon     => ":"
  | .semi      => ";"

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
      on the same list → length same, rank decreases (1→0).

    `nctx` ("negative context"): when `true`, a `-` followed by a digit
    starts a negative integer literal.  When `false`, `-` is always the
    subtract verb.  See module docstring for when each value is used. -/
def lexCore (phase : LexPhase) (chars : List Char) (pos : Nat) (nctx : Bool)
    : Except KError (List Token) :=
  match phase, chars with
  -- End of input
  | .ready, [] => .ok []
  | .digits sp acc neg, [] => .ok [mkIntToken sp pos acc neg]
  | .ident sp acc, [] => .ok [mkIdentToken sp pos acc]

  -- Accumulating digits
  | .digits sp acc neg, c :: cs =>
    if c.isDigit then
      lexCore (.digits sp (c :: acc) neg) cs (pos + 1) nctx
    else
      -- Flush the number token, re-dispatch current char
      let tok := mkIntToken sp pos acc neg
      do let rest ← lexCore .ready (c :: cs) pos false  -- just emitted a noun
         .ok (tok :: rest)

  -- Accumulating identifier
  | .ident sp acc, c :: cs =>
    if c.isAlphanum || c == '_' then
      lexCore (.ident sp (c :: acc)) cs (pos + 1) nctx
    else
      let tok := mkIdentToken sp pos acc
      do let rest ← lexCore .ready (c :: cs) pos false  -- just emitted a noun
         .ok (tok :: rest)

  -- Ready: dispatch on current character
  | .ready, c :: cs =>
    if c == ' ' || c == '\t' || c == '\n' then
      lexCore .ready cs (pos + 1) true  -- whitespace → nctx true
    else if c == '(' then
      do let rest ← lexCore .ready cs (pos + 1) true  -- after ( → nctx true
         .ok ({ kind := .lparen, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == ')' then
      do let rest ← lexCore .ready cs (pos + 1) false  -- after ) → noun
         .ok ({ kind := .rparen, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == '{' then
      do let rest ← lexCore .ready cs (pos + 1) true  -- after { → nctx true
         .ok ({ kind := .lbrace, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == '}' then
      do let rest ← lexCore .ready cs (pos + 1) false  -- after } → noun (lambda is a value)
         .ok ({ kind := .rbrace, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == '[' then
      do let rest ← lexCore .ready cs (pos + 1) true  -- after [ → nctx true
         .ok ({ kind := .lbrack, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == ']' then
      do let rest ← lexCore .ready cs (pos + 1) false  -- after ] → noun
         .ok ({ kind := .rbrack, span := ⟨pos, pos + 1⟩ } :: rest)
    else if isAdverbChar c then
      do let rest ← lexCore .ready cs (pos + 1) true  -- after adverb → nctx true
         .ok ({ kind := .adverb c, span := ⟨pos, pos + 1⟩ } :: rest)
    else if isVerbChar c then
      do let rest ← lexCore .ready cs (pos + 1) true  -- after verb → nctx true
         .ok ({ kind := .verb c, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == '-' then
      if nctx then
        -- Could be a negative literal
        match cs.head? with
        | some d =>
          if d.isDigit then
            lexCore (.digits pos [] true) cs (pos + 1) nctx
          else
            do let rest ← lexCore .ready cs (pos + 1) true
               .ok ({ kind := .verb '-', span := ⟨pos, pos + 1⟩ } :: rest)
        | none =>
          .ok [{ kind := .verb '-', span := ⟨pos, pos + 1⟩ }]
      else
        -- After a noun: always the subtract verb
        do let rest ← lexCore .ready cs (pos + 1) true
           .ok ({ kind := .verb '-', span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == ':' then
      do let rest ← lexCore .ready cs (pos + 1) true
         .ok ({ kind := .colon, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c == ';' then
      do let rest ← lexCore .ready cs (pos + 1) true
         .ok ({ kind := .semi, span := ⟨pos, pos + 1⟩ } :: rest)
    else if c.isDigit then
      lexCore (.digits pos [c] false) cs (pos + 1) nctx
    else if c.isAlpha || c == '_' then
      lexCore (.ident pos [c]) cs (pos + 1) nctx
    else
      .error { kind := .parse, message := s!"Unexpected character '{c}'",
               span := some ⟨pos, pos + 1⟩ }
termination_by (chars.length, phase.rank)
decreasing_by all_goals simp [LexPhase.rank]; omega

def tokenize (s : String) : Except KError (List Token) :=
  lexCore .ready s.toList 0 true
