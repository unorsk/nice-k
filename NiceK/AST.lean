import NiceK.Types

/-! ## Verb and Adverb Symbols

In K, the same symbol can be monadic or dyadic depending on context.
We keep symbols **unclassified** here; the evaluator decides the role. -/

inductive VerbSym where
  | plus    -- + : add (dyadic) / flip (monadic)
  | minus   -- - : subtract (dyadic) / negate (monadic)
  | bang    -- ! : mod (dyadic) / iota (monadic)
  | hash    -- # : take (dyadic) / count (monadic)
deriving BEq, Inhabited

def VerbSym.toString : VerbSym → String
  | .plus  => "+"
  | .minus => "-"
  | .bang  => "!"
  | .hash  => "#"

instance : ToString VerbSym := ⟨VerbSym.toString⟩

inductive AdverbSym where
  | each    -- '
deriving BEq, Inhabited

def AdverbSym.toString : AdverbSym → String
  | .each => "'"

instance : ToString AdverbSym := ⟨AdverbSym.toString⟩

/-- A verb is a primitive symbol optionally modified by adverbs. -/
inductive KVerb where
  | prim : VerbSym → KVerb
  | adv  : AdverbSym → KVerb → KVerb

def KVerb.toString : KVerb → String
  | .prim s   => ToString.toString s
  | .adv a v  => s!"{v.toString}{a}"

instance : ToString KVerb := ⟨KVerb.toString⟩

/-! ## Expressions -/

inductive KExpr where
  | val     : KVal → KExpr
  | var     : String → KExpr
  | monadic : KVerb → KExpr → KExpr
  | dyadic  : KVerb → KExpr → KExpr → KExpr
  | assign  : String → KExpr → KExpr        -- x:y
  | seq     : KExpr → KExpr → KExpr         -- e1;e2

def KExpr.toString : KExpr → String
  | .val v            => ToString.toString v
  | .var x            => x
  | .monadic op arg   => s!"({op} {arg.toString})"
  | .dyadic op l r    => s!"({l.toString} {op} {r.toString})"
  | .assign x rhs     => s!"({x}:{rhs.toString})"
  | .seq a b          => s!"({a.toString};{b.toString})"

instance : ToString KExpr := ⟨KExpr.toString⟩
