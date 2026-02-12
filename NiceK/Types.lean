notation "ℕ" => Nat

def KVec (n : ℕ) := Vector Int n

inductive KVal where
  | atom : Int → KVal
  | vec (n : ℕ) : KVec n → KVal
  | generic : List KVal → KVal

def KVal.toString : KVal → String
  | .atom i => s!"{i}"
  | .vec _n v => s!"{v.toList}"
  | .generic l => s!"({String.intercalate "; " (l.map toString)})"

instance : ToString KVal := ⟨KVal.toString⟩

inductive KResult (α : Type) where
  | ok : α → KResult α
  | error : String → KResult α
deriving Inhabited
