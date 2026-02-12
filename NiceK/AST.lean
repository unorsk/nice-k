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

inductive KVerb | mon (m : KMonadic) | dy (d : KDyadaic)

instance : ToString KVerb := ⟨fun v => match v with
  | .mon m => toString m
  | .dy d => toString d⟩


inductive KExpr where
  | val : KVal → KExpr                     -- A raw value (number, list)
  | var : String → KExpr                   -- A variable name (e.g., x, y)
  | dyadic : KVerb → KExpr → KExpr → KExpr -- Operator, Left, Right (e.g., 1 + 2)
  | monadic : KVerb → KExpr → KExpr        -- Operator, Right (e.g., !5)

instance : ToString KExpr := ⟨fun e => match e with
  | .val v => toString v
  | .var x => x
  | .dyadic (.dy d) l r => toString d
  | .dyadic (.mon m) l r => toString m
  | .monadic (.mon m) r => toString m
  | .monadic (.dy d) r => toString d⟩
