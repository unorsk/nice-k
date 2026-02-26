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
  | .atom i  => [.atom i]
  | .vec v   => v.toList.map .atom
  | .fatom f => [.fatom f]
  | .fvec v  => v.toList.map .fatom
  | .box l   => l
  | .str s   => [.str s]
  | .fn f    => [.fn f]

def list_to_kval : List KVal → KVal
  | []  => .box []
  | [.atom i] => .atom i
  | [.fatom f] => .fatom f
  | l   =>
    match l.mapM (fun v => match v with | .atom i => some i | _ => none) with
    | some ints => .vec ints.toArray
    | none =>
      match l.mapM (fun v => match v with | .fatom f => some f | _ => none) with
      | some floats => .fvec floats.toArray
      | none => .box l

mutual
/-- Apply a verb monadically. -/
def apply_monadic (op : KVerb) (x : KVal) : Except KError KVal :=
  match op with
  | .prim .bang  => iota x
  | .prim .hash  =>
    match x with
    | .vec v   => .ok (.atom v.size)
    | .fvec v  => .ok (.atom v.size)
    | .atom _  => .ok (.atom 1)
    | .fatom _ => .ok (.atom 1)
    | .box l   => .ok (.atom l.length)
    | .str s   => .ok (.atom s.length)
    | .fn _    => .ok (.atom 1)
  | .prim .minus => negate x
  | .prim .star  => first x
  | .prim .comma => .ok (enlist x)
  | .prim .percent => recip x
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
  | .adv .over base =>
    -- Monadic over: reduce a list with the base verb
    match x with
    | .atom _ =>
      .ok x  -- reducing a single atom returns it unchanged
    | _ =>
      let items := kval_to_list x
      match items with
      | []      => .error { kind := .domain, message := s!"{base}/ (over) requires a non-empty list" }
      | [a]     => .ok a
      | a :: as => as.foldlM (fun acc item => apply_dyadic base acc item) a
  | .adv .scan base =>
    -- Monadic scan: prefix scan over a list with the base verb
    match x with
    | .atom _ =>
      .ok x  -- scanning a single atom returns it unchanged
    | _ =>
      let items := kval_to_list x
      match items with
      | []      => .ok (.vec #[])
      | [a]     => .ok (list_to_kval [a])
      | a :: as => do
        let (_, results) ← as.foldlM (fun (acc, rs) item => do
          let next ← apply_dyadic base acc item
          pure (next, rs ++ [next])
        ) (a, [a])
        .ok (list_to_kval results)
  | .adv .eachPrior base =>
    -- Monadic each prior: apply between successive pairs (use 0 as seed for +/-)
    match x with
    | .atom _ =>
      .error { kind := .type,
               message := s!"{base}': (each prior) requires a list argument, got an atom" }
    | _ =>
      let items := kval_to_list x
      match items with
      | [] => .ok (.vec #[])
      | _  =>
        -- Use identity element 0 as seed for known operators
        let seed := KVal.atom 0
        let pairs := (seed :: items).zip items
        do let results ← pairs.mapM (fun (prev, cur) => apply_dyadic base cur prev)
           .ok (list_to_kval results)
  | .adv .eachLeft _ =>
    .error { kind := .type,
             message := s!"'{op}' (each left) must be used as a dyadic operator: x {op} y" }
  | .adv .eachRight _ =>
    .error { kind := .type,
             message := s!"'{op}' (each right) must be used as a dyadic operator: x {op} y" }

/-- Apply a verb dyadically. -/
def apply_dyadic (op : KVerb) (x y : KVal) : Except KError KVal :=
  match op with
  | .prim .plus    => add x y
  | .prim .minus   => sub x y
  | .prim .star    => mul x y
  | .prim .percent => kdiv x y
  | .prim .comma   => join x y
  | .prim .bang  =>
    .error { kind := .type,
             message := "Dyadic '!' (mod/key) not yet implemented" }
  | .prim .hash => take_ x y
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
  | .adv .eachRight base =>
    -- Each right: x f/: y → for each item yi in y, compute f(x, yi)
    let items := kval_to_list y
    do let results ← items.mapM (fun item => apply_dyadic base x item)
       .ok (list_to_kval results)
  | .adv .eachLeft base =>
    -- Each left: x f\: y → for each item xi in x, compute f(xi, y)
    let items := kval_to_list x
    do let results ← items.mapM (fun item => apply_dyadic base item y)
       .ok (list_to_kval results)
  | .adv .eachPrior base =>
    -- Dyadic each prior: left arg is seed, apply between successive pairs of right
    let items := kval_to_list y
    match items with
    | [] => .ok (.vec #[])
    | _  =>
      let pairs := (x :: items).zip items
      do let results ← pairs.mapM (fun (prev, cur) => apply_dyadic base cur prev)
         .ok (list_to_kval results)
  | .adv .over base =>
    -- Dyadic over: x f/ y → fold y starting from x with f
    let items := kval_to_list y
    items.foldlM (fun acc item => apply_dyadic base acc item) x
  | .adv .scan base =>
    -- Dyadic scan: x f\ y → prefix scan starting from x with f
    let items := kval_to_list y
    match items with
    | [] => .ok (list_to_kval [x])
    | _  => do
      let (_, results) ← items.foldlM (fun (acc, rs) item => do
        let next ← apply_dyadic base acc item
        pure (next, rs ++ [next])
      ) (x, [x])
      .ok (list_to_kval results)
end

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
  | .derive _ e       => implicitArity e
  | _                 => 0

/-- Determine the parameter names for implicit params given arity. -/
private def implicitParamNames : Nat → List String
  | 0 => []
  | 1 => ["x"]
  | 2 => ["x", "y"]
  | _ => ["x", "y", "z"]

/-- Evaluate an expression in a stateful environment.
    `partial` because function application evaluates a body that is not
    structurally smaller than the call-site expression.
    `applyKFn` centralizes function application for both primitive verbs
    and user-defined functions, enabling iterators on lambdas. -/
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
  | .list es => do
    let vs ← es.mapM (fun e => eval e)
    pure (list_to_kval vs)
  | .derive adv inner => do
    let v ← eval inner
    match v with
    | .fn baseFn => pure (.fn (.derived adv baseFn))
    | _ => throwE { kind := .type,
                    message := s!"Iterator '{adv}' requires a function, got {v}" }
  | .app fExpr argExprs => do
    let argVals ← argExprs.mapM (fun a => eval a)
    let fVal ← withCtx "in function position" (eval fExpr)
    match fVal with
    | .fn f => applyKFn f argVals
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
where
  applyKFn (f : KFn) (args : List KVal) : EvalM KVal :=
    match f with
    | .user params arity body closure =>
      if args.length != arity then
        throwE { kind := .type,
                 message := s!"Function expects {arity} argument(s), got {args.length}" }
      else
        let paramNames := match params with
          | .explicit names => names
          | .implicit       => implicitParamNames arity
        let bindings := paramNames.zip args
        let callEnv := bindings ++ closure
        withCtx "in function body" (liftE ((eval body callEnv).map (·.1)))
    | .primVerb v =>
      match args with
      | [x]    => withCtx s!"in monadic '{v}'" (liftE (apply_monadic v x))
      | [x, y] => withCtx s!"in dyadic '{v}'" (liftE (apply_dyadic v x y))
      | _      => throwE { kind := .type,
                           message := s!"Verb '{v}' expects 1 or 2 arguments, got {args.length}" }
    | .derived adv base => applyDerived adv base args
    | .train2 f g =>
      match args with
      | [x] => do
        let gx ← withCtx "in g of monadic train" (applyKFn g [x])
        withCtx "in f of monadic train" (applyKFn f [gx])
      | [x, y] => do
        let xgy ← withCtx "in g of dyadic train" (applyKFn g [x, y])
        withCtx "in f of dyadic train" (applyKFn f [xgy])
      | _ =>
        throwE { kind := .type,
                 message := s!"Train expects 1 or 2 argument(s), got {args.length}" }
  applyDerived (adv : AdverbSym) (base : KFn) (args : List KVal) : EvalM KVal :=
    let applyBinary (x y : KVal) : EvalM KVal := applyKFn base [x, y]
    let applyUnary (x : KVal) : EvalM KVal := applyKFn base [x]
    match adv, args with
    -- Each (monadic): apply base to each item
    | .each, [x] =>
      match x with
      | .atom _ => applyUnary x
      | _ =>
        let items := kval_to_list x
        do let results ← items.mapM applyUnary
           pure (list_to_kval results)
    -- Each (dyadic / each-both): apply base to corresponding items
    | .each, [x, y] =>
      match x, y with
      | .atom _, .atom _ => applyBinary x y
      | .atom a, _ =>
        let items := kval_to_list y
        do let results ← items.mapM (fun item => applyBinary (.atom a) item)
           pure (list_to_kval results)
      | _, .atom a =>
        let items := kval_to_list x
        do let results ← items.mapM (fun item => applyBinary item (.atom a))
           pure (list_to_kval results)
      | _, _ =>
        let left_items := kval_to_list x
        let right_items := kval_to_list y
        if left_items.length != right_items.length then
          throwE { kind := .length,
                   message := s!"{base}' (each) requires lists of equal length, got {left_items.length} and {right_items.length}" }
        else do
          let results ← (left_items.zip right_items).mapM (fun (l, r) => applyBinary l r)
          pure (list_to_kval results)
    -- Each Right: x f/: y → for each yi, f(x, yi)
    | .eachRight, [x, y] =>
      let items := kval_to_list y
      do let results ← items.mapM (fun item => applyBinary x item)
         pure (list_to_kval results)
    -- Each Left: x f\: y → for each xi, f(xi, y)
    | .eachLeft, [x, y] =>
      let items := kval_to_list x
      do let results ← items.mapM (fun item => applyBinary item y)
         pure (list_to_kval results)
    -- Each Prior (monadic): seed = 0
    | .eachPrior, [y] =>
      let items := kval_to_list y
      match items with
      | [] => pure (.vec #[])
      | _ =>
        let seed := KVal.atom 0
        let pairs := (seed :: items).zip items
        do let results ← pairs.mapM (fun (prev, cur) => applyBinary cur prev)
           pure (list_to_kval results)
    -- Each Prior (dyadic): left is seed
    | .eachPrior, [x, y] =>
      let items := kval_to_list y
      match items with
      | [] => pure (.vec #[])
      | _ =>
        let pairs := (x :: items).zip items
        do let results ← pairs.mapM (fun (prev, cur) => applyBinary cur prev)
           pure (list_to_kval results)
    -- Over (monadic): reduce
    | .over, [x] =>
      match x with
      | .atom _ => pure x
      | _ =>
        let items := kval_to_list x
        match items with
        | [] => throwE { kind := .domain, message := s!"{base}/ (over) requires a non-empty list" }
        | [a] => pure a
        | a :: as => do
          let mut acc := a
          for item in as do
            acc ← applyBinary acc item
          pure acc
    -- Over (dyadic): fold with seed
    | .over, [x, y] =>
      let items := kval_to_list y
      do let mut acc := x
         for item in items do
           acc ← applyBinary acc item
         pure acc
    -- Scan (monadic): prefix scan
    | .scan, [x] =>
      match x with
      | .atom _ => pure x
      | _ =>
        let items := kval_to_list x
        match items with
        | [] => pure (.vec #[])
        | [a] => pure (list_to_kval [a])
        | a :: as => do
          let mut acc := a
          let mut results := [a]
          for item in as do
            acc ← applyBinary acc item
            results := results ++ [acc]
          pure (list_to_kval results)
    -- Scan (dyadic): prefix scan with seed
    | .scan, [x, y] =>
      let items := kval_to_list y
      match items with
      | [] => pure (list_to_kval [x])
      | _ => do
        let mut acc := x
        let mut results := [x]
        for item in items do
          acc ← applyBinary acc item
          results := results ++ [acc]
        pure (list_to_kval results)
    | _, _ =>
      throwE { kind := .type,
               message := s!"Iterator '{adv}' cannot be applied with {args.length} argument(s)" }

/-- Run evaluation with an initial environment, returning only the value. -/
def evalIn (env : KEnv) (e : KExpr) : Except KError KVal :=
  (eval e env).map (fun (v, _) => v)

/-- Run evaluation with an initial environment, returning both value and final env. -/
def evalWithEnv (env : KEnv) (e : KExpr) : Except KError (KVal × KEnv) :=
  eval e env
