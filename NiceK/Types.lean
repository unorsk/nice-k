notation "ℕ" => Nat


def KVec : Type := Array Int

inductive KVal where
  | atom : Int → KVal
  | vec : Array Int → KVal
  | generic : List KVal → KVal

def KVal.toString : KVal → String
  | .atom i => s!"{i}"
  | .vec v => s!"{v.toList}"
  | .generic l => s!"({String.intercalate "; " (l.map toString)})"

instance : ToString KVal := ⟨KVal.toString⟩

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
