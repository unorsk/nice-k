import NiceK.Types
import Lean.Parser
import Init.Data.Repr

inductive KDyadaic | add --| sub | mul | take

instance : ToString KDyadaic := ⟨fun d => match d with
  | .add => "+"⟩

inductive KMonadic | iota | count --| neg

instance : ToString KMonadic := ⟨fun m => match m with
  | .iota => "iota"
  | .count => "count"⟩

inductive KAdverb | each

instance : ToString KAdverb := ⟨fun a => match a with
  | .each => "'"⟩

inductive KVerb
  | mon (m : KMonadic)
  | dy (d : KDyadaic)
  | adv (a : KAdverb) (v : KVerb)

def KVerb.toString : KVerb → String
  | .mon m => ToString.toString m
  | .dy d => ToString.toString d
  | .adv a v => s!"{v.toString}{a}"

instance : ToString KVerb := ⟨KVerb.toString⟩


inductive KExpr where
  | val : KVal → KExpr                     -- A raw value (number, list)
  | var : String → KExpr                   -- A variable name (e.g., x, y)
  | dyadic : KVerb → KExpr → KExpr → KExpr -- Operator, Left, Right (e.g., 1 + 2)
  | monadic : KVerb → KExpr → KExpr        -- Operator, Right (e.g., !5)

instance : ToString KExpr := ⟨fun e => match e with
  | .val v => ToString.toString v
  | .var x => x
  | .dyadic op _ _ => ToString.toString op
  | .monadic op _ => ToString.toString op⟩
