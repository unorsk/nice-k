notation "ℕ" => Nat


def KVec : Type := Array Int

/-! ## Error types -/

inductive KErrorKind where
  | parse
  | length
  | domain
  | type
  | syntax
  | value
deriving Inhabited, BEq

def KErrorKind.toString : KErrorKind → String
  | .parse   => "Parse Error"
  | .length  => "Length Error"
  | .domain  => "Domain Error"
  | .type    => "Type Error"
  | .syntax  => "Syntax Error"
  | .value   => "Value Error"

instance : ToString KErrorKind := ⟨KErrorKind.toString⟩

structure SourceSpan where
  start : Nat
  stop  : Nat
deriving Inhabited, BEq

def SourceSpan.toString (s : SourceSpan) : String :=
  s!"{s.start}..{s.stop}"

instance : ToString SourceSpan := ⟨SourceSpan.toString⟩

structure KError where
  kind    : KErrorKind
  message : String
  span    : Option SourceSpan := none
  context : List String := []
deriving Inhabited

def KError.toString (e : KError) : String :=
  let base := s!"{e.kind}: {e.message}"
  let withSpan := match e.span with
    | some s => s!"{base} at {s}"
    | none   => base
  match e.context with
  | [] => withSpan
  | ctx => s!"{withSpan}\n  in {String.intercalate "\n  in " ctx}"

instance : ToString KError := ⟨KError.toString⟩

def KError.withContext (e : KError) (ctx : String) : KError :=
  { e with context := ctx :: e.context }

/-! ## Verb and Adverb Symbols

In K, the same symbol can be monadic or dyadic depending on context.
We keep symbols **unclassified** here; the evaluator decides the role. -/

inductive VerbSym where
  | plus    -- + : add (dyadic) / flip (monadic)
  | minus   -- - : subtract (dyadic) / negate (monadic)
  | star    -- * : multiply (dyadic) / first (monadic)
  | bang    -- ! : mod (dyadic) / iota (monadic)
  | hash    -- # : take (dyadic) / count (monadic)
deriving BEq, Inhabited

def VerbSym.toString : VerbSym → String
  | .plus  => "+"
  | .minus => "-"
  | .star  => "*"
  | .bang  => "!"
  | .hash  => "#"

instance : ToString VerbSym := ⟨VerbSym.toString⟩

inductive AdverbSym where
  | each        -- '   : map over items
  | eachRight   -- /:  : map fixing left, iterating right
  | eachLeft    -- \:  : map fixing right, iterating left
  | eachPrior   -- ':  : apply between successive pairs
  | over        -- /   : reduce (fold)
  | scan        -- \   : prefix scan (fold keeping intermediates)
deriving BEq, Inhabited

def AdverbSym.toString : AdverbSym → String
  | .each      => "'"
  | .eachRight => "/:"
  | .eachLeft  => "\\:"
  | .eachPrior => "':"
  | .over      => "/"
  | .scan      => "\\"

instance : ToString AdverbSym := ⟨AdverbSym.toString⟩

/-- A verb is a primitive symbol optionally modified by adverbs. -/
inductive KVerb where
  | prim : VerbSym → KVerb
  | adv  : AdverbSym → KVerb → KVerb

def KVerb.toString : KVerb → String
  | .prim s   => ToString.toString s
  | .adv a v  => s!"{v.toString}{a}"

instance : ToString KVerb := ⟨KVerb.toString⟩

/-! ## Lambda parameter specification -/

inductive ParamSpec where
  | explicit (names : List String)   -- {[x;y] ...}
  | implicit                         -- {...} uses x y z
deriving Inhabited, BEq

/-! ## Core types: KVal, KFn, KExpr

KVal and KExpr are mutually recursive: a KVal can hold a function
whose body is a KExpr, and a KExpr literal wraps a KVal.  We define
them together in a `mutual` block. -/

mutual
inductive KVal where
  | atom : Int → KVal
  | vec  : Array Int → KVal
  | box  : List KVal → KVal
  | fn   : KFn → KVal

inductive KFn where
  | user (params : ParamSpec) (arity : Nat) (body : KExpr) (closure : List (String × KVal))
  | primVerb (v : KVerb)
  | derived (adv : AdverbSym) (base : KFn)

inductive KExpr where
  | val     : KVal → KExpr
  | var     : String → KExpr
  | lam     : ParamSpec → KExpr → KExpr           -- {[params] body}
  | app     : KExpr → List KExpr → KExpr          -- f[args]
  | monadic : KVerb → KExpr → KExpr
  | dyadic  : KVerb → KExpr → KExpr → KExpr
  | assign  : String → KExpr → KExpr              -- x:y
  | seq     : KExpr → KExpr → KExpr               -- e1;e2
  | derive  : AdverbSym → KExpr → KExpr           -- expr + adverb (e.g. {x+y}/)
end

mutual
def KVal.toString : KVal → String
  | .atom i => s!"{i}"
  | .vec v  => s!"{v.toList}"
  | .box l  => s!"({String.intercalate "; " (l.map KVal.toString)})"
  | .fn f   => KFn.toString f

def KFn.toString : KFn → String
  | .user _params _arity body _closure => s!"\{{KExpr.toString body}}"
  | .primVerb v => KVerb.toString v
  | .derived a base => s!"{KFn.toString base}{a}"

def KExpr.toString : KExpr → String
  | .val v            => KVal.toString v
  | .var x            => x
  | .lam params body  =>
    let ps := match params with
      | .explicit names => s!"[{String.intercalate ";" names}] "
      | .implicit => ""
    s!"\{{ps}{KExpr.toString body}}"
  | .app f args       =>
    let argStrs := args.map KExpr.toString
    s!"{KExpr.toString f}[{String.intercalate ";" argStrs}]"
  | .monadic op arg   => s!"({op} {KExpr.toString arg})"
  | .dyadic op l r    => s!"({KExpr.toString l} {op} {KExpr.toString r})"
  | .assign x rhs     => s!"({x}:{KExpr.toString rhs})"
  | .seq a b          => s!"({KExpr.toString a};{KExpr.toString b})"
  | .derive a e       => s!"{KExpr.toString e}{a}"
end

instance : ToString KVal := ⟨KVal.toString⟩
instance : ToString KFn := ⟨KFn.toString⟩
instance : ToString KExpr := ⟨KExpr.toString⟩
