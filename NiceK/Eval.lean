import NiceK.Types
import NiceK.AST
import NiceK.Ops

private def withCtx (ctx : String) (m : Except KError α) : Except KError α :=
  m.mapError (·.withContext ctx)

def kval_to_list : KVal → List KVal
  | .atom i => [.atom i]
  | .vec n v => (v.toList).map .atom
  | .generic l => l

def list_to_kval (l : List KVal) : KVal :=
  let n := l.length
  match l.mapM (fun v => match v with | .atom i => some i | _ => none) with
  | some ints => .vec n (Vector.ofFn (fun i => ints[i.val]!))
  | none => .generic l

def apply_monadic (op : KVerb) (x : KVal) : Except KError KVal := do
  match op with
  | .mon .count =>
    match x with
    | .vec _n v => .ok (.atom v.size)
    | .atom _i  => .ok (.atom 1)
    | .generic l => .ok (.atom l.length)
  | .mon .iota => iota x
  | .dy _ => throw { kind := .syntax, message := "Dyadic verb used in monadic position" }
  | .adv .each base =>
    match x with
    | .atom _ =>
      let msg := s!"{base}' (each) requires a list argument, got an atom"
      throw { kind := .type, message := msg }
    | _ =>
      let items := kval_to_list x
      let results ← items.mapM (fun item => apply_monadic base item)
      return list_to_kval results

def apply_dyadic (op : KVerb) (x y : KVal) : Except KError KVal := do
  match op with
  | .dy .add => add x y
  | .mon _ => throw { kind := .syntax, message := "Monadic verb used in dyadic position" }
  | .adv .each base =>
    match x, y with
    | .atom _, .atom _ =>
      let msg := s!"{base}' (each) requires at least one list argument, got two atoms"
      throw { kind := .type, message := msg }
    | .atom a, _ =>
      let items := kval_to_list y
      let results ← items.mapM (fun item => apply_dyadic base (.atom a) item)
      return list_to_kval results
    | _, .atom a =>
      let items := kval_to_list x
      let results ← items.mapM (fun item => apply_dyadic base item (.atom a))
      return list_to_kval results
    | _, _ =>
      let left_items := kval_to_list x
      let right_items := kval_to_list y
      if left_items.length != right_items.length then
        let msg := s!"{base}' (each) requires lists of equal length, got {left_items.length} and {right_items.length}"
        throw { kind := .length, message := msg }
      else
        let results ← (left_items.zip right_items).mapM (fun (l, r) => apply_dyadic base l r)
        return list_to_kval results

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
