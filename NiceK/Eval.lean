import NiceK.Types
import NiceK.AST
import NiceK.Ops

def apply_monadic (op : KVerb) (x : KVal) : KResult KVal :=
  match op with
  | .mon .count =>
    match x with
    | .vec _n v => .ok (.atom v.size)
    | .atom _i  => .ok (.atom 1)
    | .generic l => .ok (.atom l.length)
  | .mon .iota => iota x
  | .dy _ => .error "Syntax Error: Dyadic verb used in monadic position"

def apply_dyadic (op : KVerb) (x y : KVal) : KResult KVal :=
  match op with
  | .dy .add => add x y
  | .mon _ => .error "Syntax Error: Monadic verb used in dyadic position"

def eval (e : KExpr) : KResult KVal :=
  match e with
  | .val v => .ok v
  | .var _ => .error "Value Error: Variables not implemented"
  | .monadic op e_right =>
     match eval e_right with
     | .ok v_right => apply_monadic op v_right
     | .error err => .error err
  | .dyadic op e_left e_right =>
     match eval e_left with
     | .error err => .error err
     | .ok v_left =>
       match eval e_right with
       | .error err => .error err
       | .ok v_right => apply_dyadic op v_left v_right
