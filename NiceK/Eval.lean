import NiceK.Types
import NiceK.AST
import NiceK.Ops

def apply_monadic (op : String) (x : KVal) : KResult KVal :=
  match op, x with
  | "!", .atom i =>
      if i < 0 then .error "Domain Error: '!' requires non-negative"
      else .ok (.vec i.toNat (iota_core i.toNat))
  | "!", _ => .error "Type Error: '!' not implemented for this type"
  | _, _ => .error s!"Syntax Error: Unknown monadic operator '{op}'"

def apply_dyadic (op : String) (x y : KVal) : KResult KVal :=
  match op with
  | "+" =>
    match x, y with
    | .atom a, .atom b => .ok (.atom (a + b))
    | .vec n v1, .vec m v2 =>
        if h : n = m then
           .ok (.vec n (add_vectors_core v1 (h ▸ v2)))
        else .error "Length Error"
    | .atom a, .vec n v => .ok (.vec n (add_vectors_core (Vector.replicate n a) v))
    | .vec n v, .atom b => .ok (.vec n (add_vectors_core v (Vector.replicate n b)))
    | _, _ => .error "Type Error generic"
  | _ => .error s!"Syntax Error: Unknown dyadic operator '{op}'"

partial def eval (e : KExpr) : KResult KVal :=
  match e with
  | .val v => .ok v
  | .var _ => .error "Value Error: Variables not implemented"
  | .monadic op e_right =>
      match eval e_right with
      | .ok v_right => apply_monadic op v_right
      | .error err => .error err
  | .dyadic op e_left e_right =>
      -- Evaluate Left
      match eval e_left with
      | .error err => .error err
      | .ok v_left =>
        -- Evaluate Right
        match eval e_right with
        | .error err => .error err
        | .ok v_right => apply_dyadic op v_left v_right
