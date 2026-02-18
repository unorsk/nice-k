import NiceK.Types
import NiceK.AST
import NiceK.Ops

private def withCtx (ctx : String) (m : Except KError α) : Except KError α :=
  m.mapError (·.withContext ctx)

def apply_monadic (op : KVerb) (x : KVal) : Except KError KVal :=
  match op with
  | .mon .count =>
    match x with
    | .vec _n v => .ok (.atom v.size)
    | .atom _i  => .ok (.atom 1)
    | .generic l => .ok (.atom l.length)
  | .mon .iota => iota x
  | .dy _ => throw { kind := .syntax, message := "Dyadic verb used in monadic position" }

def apply_dyadic (op : KVerb) (x y : KVal) : Except KError KVal :=
  match op with
  | .dy .add => add x y
  | .mon _ => throw { kind := .syntax, message := "Monadic verb used in dyadic position" }

def eval (e : KExpr) : Except KError KVal := do
  match e with
  | .val v => return v
  | .var _ => throw { kind := .value, message := "Variables not implemented" }
  | .monadic op e_right =>
      let v_right ← withCtx s!"in argument of monadic '{op}'" (eval e_right)
      withCtx s!"in monadic '{op}'" (apply_monadic op v_right)
  | .dyadic op e_left e_right =>
      let v_left  ← withCtx s!"in left operand of '{op}'"  (eval e_left)
      let v_right ← withCtx s!"in right operand of '{op}'" (eval e_right)
      withCtx s!"in dyadic '{op}'" (apply_dyadic op v_left v_right)
