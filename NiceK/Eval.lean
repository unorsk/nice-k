import NiceK.Types
import NiceK.AST
import NiceK.Primitives

/-! ## Evaluator

Key design choices:
- **Right-to-left evaluation**: for dyadic ops, the right operand is
  evaluated before the left.  This is invisible today (no side effects)
  but will matter once assignment is added.
- **Environment plumbing**: `KEnv` is threaded through for future
  variable support.
- Verb dispatch is based on `VerbSym`, deciding monadic vs dyadic
  at the call site. -/

abbrev KEnv := List (String × KVal)

private def withCtx (ctx : String) (m : Except KError α) : Except KError α :=
  m.mapError (·.withContext ctx)

def kval_to_list : KVal → List KVal
  | .atom i    => [.atom i]
  | .vec v  => v.toList.map .atom
  | .box l => l

def list_to_kval : List KVal → KVal
  | []  => .box []
  | [.atom i] => .atom i
  | l   =>
    match l.mapM (fun v => match v with | .atom i => some i | _ => none) with
    | some ints => .vec ints.toArray
    | none => .box l

/-- Apply a verb monadically. -/
def apply_monadic (op : KVerb) (x : KVal) : Except KError KVal :=
  match op with
  | .prim .bang  => iota x
  | .prim .hash  =>
    match x with
    | .vec v   => .ok (.atom v.size)
    | .atom _     => .ok (.atom 1)
    | .box l  => .ok (.atom l.length)
  | .prim .minus => negate x
  | .prim .plus  =>
    -- monadic + is "flip" for tables; for atoms/vecs it's identity
    .ok x
  | .adv .each base =>
    match x with
    | .atom _ =>
      .error { kind := .type,
               message := s!"{base}' (each) requires a list argument, got an atom" }
    | _ =>
      let items := kval_to_list x
      do let results ← items.mapM (fun item => apply_monadic base item)
         .ok (list_to_kval results)

/-- Apply a verb dyadically. -/
def apply_dyadic (op : KVerb) (x y : KVal) : Except KError KVal :=
  match op with
  | .prim .plus  => add x y
  | .prim .minus => sub x y
  | .prim .bang  =>
    .error { kind := .type,
             message := "Dyadic '!' (mod/key) not yet implemented" }
  | .prim .hash =>
    .error { kind := .type,
             message := "Dyadic '#' (take/reshape) not yet implemented" }
  | .adv .each base =>
    match x, y with
    | .atom _, .atom _ =>
      .error { kind := .type,
               message := s!"{base}' (each) requires at least one list argument, got two atoms" }
    | .atom a, _ =>
      let items := kval_to_list y
      do let results ← items.mapM (fun item => apply_dyadic base (.atom a) item)
         .ok (list_to_kval results)
    | _, .atom a =>
      let items := kval_to_list x
      do let results ← items.mapM (fun item => apply_dyadic base item (.atom a))
         .ok (list_to_kval results)
    | _, _ =>
      let left_items := kval_to_list x
      let right_items := kval_to_list y
      if left_items.length != right_items.length then
        .error { kind := .length,
                 message := s!"{base}' (each) requires lists of equal length, got {left_items.length} and {right_items.length}" }
      else do
        let results ← (left_items.zip right_items).mapM (fun (l, r) => apply_dyadic base l r)
        .ok (list_to_kval results)

/-- Evaluate an expression in an environment.
    Right-to-left: for dyadic ops, right operand is evaluated first. -/
def eval (env : KEnv) (e : KExpr) : Except KError KVal :=
  match e with
  | .val v => .ok v
  | .var name =>
    match env.lookup name with
    | some v => .ok v
    | none   => .error { kind := .value, message := s!"Undefined variable '{name}'" }
  | .monadic op e_right =>
    do let v_right ← withCtx s!"in argument of monadic '{op}'" (eval env e_right)
       withCtx s!"in monadic '{op}'" (apply_monadic op v_right)
  | .dyadic op e_left e_right =>
    -- Right-to-left: evaluate right first
    do let v_right ← withCtx s!"in right operand of '{op}'" (eval env e_right)
       let v_left  ← withCtx s!"in left operand of '{op}'"  (eval env e_left)
       withCtx s!"in dyadic '{op}'" (apply_dyadic op v_left v_right)
