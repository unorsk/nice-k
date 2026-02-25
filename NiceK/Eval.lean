import NiceK.Types
import NiceK.AST
import NiceK.Primitives

/-! ## Evaluator

Key design choices:
- **Right-to-left evaluation**: for dyadic ops, the right operand is
  evaluated before the left.  This is now observable via assignment.
- **StateT-based environment**: `EvalM` threads `KEnv` via `StateT`,
  supporting assignment (`:`) and sequencing (`;`).
- Verb dispatch is based on `VerbSym`, deciding monadic vs dyadic
  at the call site. -/

abbrev KEnv := List (String × KVal)
abbrev EvalM := StateT KEnv (Except KError)

private def throwE (e : KError) : EvalM α :=
  fun _ => .error e

private def liftE (m : Except KError α) : EvalM α :=
  fun st => m.map (fun a => (a, st))

private def withCtx (ctx : String) (m : EvalM α) : EvalM α :=
  fun st => (m st).mapError (·.withContext ctx)

def kval_to_list : KVal → List KVal
  | .atom i => [.atom i]
  | .vec v  => v.toList.map .atom
  | .box l  => l
  | .fn f   => [.fn f]

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
    | .atom _  => .ok (.atom 1)
    | .box l   => .ok (.atom l.length)
    | .fn _    => .ok (.atom 1)
  | .prim .minus => negate x
  | .prim .plus  =>
    -- monadic + is "flip" (transpose); atoms/vecs can't be flipped
    match x with
    | .box _ => .error { kind := .type, message := "'+' (flip) not yet implemented for nested lists" }
    | _ => .error { kind := .type, message := "'+' (flip) requires a list of lists, got an atom or flat vector" }
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

/-! ### Implicit parameter arity inference

Scans a `KExpr` for uses of `x`, `y`, `z` (the implicit parameters).
Does **not** recurse into nested lambdas, since those have their own scope. -/

private def implicitArity : KExpr → Nat
  | .var "x"          => 1
  | .var "y"          => 2
  | .var "z"          => 3
  | .lam _ _          => 0   -- stop at nested lambda
  | .app f as         => max (implicitArity f) (as.foldl (fun m a => max m (implicitArity a)) 0)
  | .monadic _ e      => implicitArity e
  | .dyadic _ l r     => max (implicitArity l) (implicitArity r)
  | .assign _ rhs     => implicitArity rhs
  | .seq a b          => max (implicitArity a) (implicitArity b)
  | _                 => 0

/-- Determine the parameter names for implicit params given arity. -/
private def implicitParamNames : Nat → List String
  | 0 => []
  | 1 => ["x"]
  | 2 => ["x", "y"]
  | _ => ["x", "y", "z"]

/-- Evaluate an expression in a stateful environment.
    `partial` because function application evaluates a body that is not
    structurally smaller than the call-site expression. -/
partial def eval : KExpr → EvalM KVal
  | .val v => pure v
  | .var name => do
    let env ← get
    match env.lookup name with
    | some v => pure v
    | none   => throwE { kind := .value, message := s!"Undefined variable '{name}'" }
  | .assign name rhs => do
    let v ← withCtx s!"in RHS of assignment '{name}:'" (eval rhs)
    modify (fun env => (name, v) :: env)
    pure v
  | .seq e1 e2 => do
    let _ ← withCtx "in left of ';'" (eval e1)
    withCtx "in right of ';'" (eval e2)
  | .lam params body => do
    let env ← get
    let arity := match params with
      | .explicit names => names.length
      | .implicit       => implicitArity body
    pure (.fn (.user params arity body env))
  | .app fExpr argExprs => do
    let argVals ← argExprs.mapM (fun a => eval a)
    let fVal ← withCtx "in function position" (eval fExpr)
    match fVal with
    | .fn (.user params arity body closure) =>
      if argVals.length != arity then
        throwE { kind := .type,
                 message := s!"Function expects {arity} argument(s), got {argVals.length}" }
      else
        let paramNames := match params with
          | .explicit names => names
          | .implicit       => implicitParamNames arity
        let bindings := paramNames.zip argVals
        let callEnv := bindings ++ closure
        withCtx "in function body" (liftE ((eval body callEnv).map (·.1)))
    | .fn (.primVerb v) =>
      match argVals with
      | [x]    => withCtx s!"in monadic '{v}'" (liftE (apply_monadic v x))
      | [x, y] => withCtx s!"in dyadic '{v}'" (liftE (apply_dyadic v x y))
      | _      => throwE { kind := .type,
                           message := s!"Verb '{v}' expects 1 or 2 arguments, got {argVals.length}" }
    | _ => throwE { kind := .type,
                    message := s!"Cannot call a non-function value" }
  | .monadic op e_right => do
    let v_right ← withCtx s!"in argument of monadic '{op}'" (eval e_right)
    withCtx s!"in monadic '{op}'" (liftE (apply_monadic op v_right))
  | .dyadic op e_left e_right => do
    -- Right-to-left: evaluate right first
    let v_right ← withCtx s!"in right operand of '{op}'" (eval e_right)
    let v_left  ← withCtx s!"in left operand of '{op}'"  (eval e_left)
    withCtx s!"in dyadic '{op}'" (liftE (apply_dyadic op v_left v_right))

/-- Run evaluation with an initial environment, returning only the value. -/
def evalIn (env : KEnv) (e : KExpr) : Except KError KVal :=
  (eval e env).map (fun (v, _) => v)

/-- Run evaluation with an initial environment, returning both value and final env. -/
def evalWithEnv (env : KEnv) (e : KExpr) : Except KError (KVal × KEnv) :=
  eval e env
