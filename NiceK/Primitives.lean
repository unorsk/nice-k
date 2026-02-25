import NiceK.Types

def add_vectors_core (v1 : KVec) (v2 : KVec) : KVec :=
  v1.zipWith (· + ·) v2

def sub_vectors_core (v1 : KVec) (v2 : KVec) : KVec :=
  v1.zipWith (· - ·) v2

def add (a b : KVal) : Except KError KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok (.atom (x + y))

  | .vec v1, .vec v2 =>
      if v1.size = v2.size then
        .ok (.vec (add_vectors_core v1 v2))
      else
        .error { kind := .length, message := s!"Cannot add vector of length {v1.size} to vector of length {v2.size}" }

  | .atom x, .vec v =>
      let scalar_vec := Array.replicate v.size x
      .ok (.vec $ add_vectors_core scalar_vec v)

  | .vec v, .atom y =>
      let scalar_vec := Array.replicate v.size y
      .ok (.vec $ add_vectors_core v scalar_vec)

  | .fatom _, _ | _, .fatom _ | .fvec _, _ | _, .fvec _ =>
      .error { kind := .type, message := "'+' not yet implemented for float values" }
  | .box _, _ | _, .box _ => .error { kind := .type, message := "'+' not yet implemented for box values" }
  | .str _, _ | _, .str _ => .error { kind := .type, message := "'+' not supported on strings" }
  | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'+' not supported on functions" }

def negate (x : KVal) : Except KError KVal :=
  match x with
  | .atom i  => .ok (.atom (-i))
  | .vec v   => .ok (.vec (Array.map (- ·) v))
  | .fatom f => .ok (.fatom (-f))
  | .fvec v  => .ok (.fvec (Array.map (- ·) v))
  | .box _   => .error { kind := .type, message := "'-' (negate) not yet implemented for box values" }
  | .str _   => .error { kind := .type, message := "'-' (negate) not supported on strings" }
  | .fn _    => .error { kind := .type, message := "'-' (negate) not supported on functions" }

def sub (a b : KVal) : Except KError KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok (.atom (x - y))

  | .vec v1, .vec v2 =>
      if v1.size = v2.size then
        .ok (.vec $ sub_vectors_core v1 v2)
      else
        .error { kind := .length, message := s!"Cannot subtract vector of length {v1.size} from vector of length {v2.size}" }

  | .atom x, .vec v =>
      let scalar_vec := Array.replicate v.size x
      .ok (.vec (sub_vectors_core scalar_vec v))

  | .vec v, .atom y =>
      let scalar_vec := Array.replicate v.size y
      .ok (.vec $ sub_vectors_core v scalar_vec)

  | .fatom _, _ | _, .fatom _ | .fvec _, _ | _, .fvec _ =>
      .error { kind := .type, message := "'-' not yet implemented for float values" }
  | .box _, _ | _, .box _ => .error { kind := .type, message := "'-' not yet implemented for box values" }
  | .str _, _ | _, .str _ => .error { kind := .type, message := "'-' not supported on strings" }
  | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'-' not supported on functions" }

def mul_vectors_core (v1 : KVec) (v2 : KVec) : KVec :=
  v1.zipWith (· * ·) v2

def mul (a b : KVal) : Except KError KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok $ .atom (x * y)

  | .vec v1, .vec v2 =>
      if v1.size = v2.size then
        .ok $ .vec (mul_vectors_core v1 v2)
      else
        .error { kind := .length, message := s!"Cannot multiply vector of length {v1.size} by vector of length {v2.size}" }

  | .atom x, .vec v =>
      let scalar_vec := Array.replicate v.size x
      .ok $ .vec $ mul_vectors_core scalar_vec v

  | .vec v, .atom y =>
      let scalar_vec := Array.replicate v.size y
      .ok $ .vec $ mul_vectors_core v scalar_vec

  | .fatom _, _ | _, .fatom _ | .fvec _, _ | _, .fvec _ =>
      .error { kind := .type, message := "'*' not yet implemented for float values" }
  | .box _, _ | _, .box _ => .error { kind := .type, message := "'*' not yet implemented for box values" }
  | .str _, _ | _, .str _ => .error { kind := .type, message := "'*' not supported on strings" }
  | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'*' not supported on functions" }

def first (x : KVal) : Except KError KVal :=
  match x with
  | .atom i  => .ok $ .atom i
  | .fatom f => .ok $ .fatom f
  | .vec v   =>
    if v.size == 0 then
      .error { kind := .domain, message := "'*' (first) requires a non-empty list" }
    else
      .ok $ .atom v[0]!
  | .fvec v  =>
    if v.size == 0 then
      .error { kind := .domain, message := "'*' (first) requires a non-empty list" }
    else
      .ok $ .fatom v[0]!
  | .box l   =>
    match l with
    | []     => .error { kind := .domain, message := "'*' (first) requires a non-empty list" }
    | a :: _ => .ok a
  | .str s   =>
    if s.isEmpty then
      .error { kind := .domain, message := "'*' (first) requires a non-empty string" }
    else
      .ok $ .str s.front.toString
  | .fn f    => .ok $ .fn f

def enlist (x : KVal) : KVal := .box [x]

private def toList : KVal → List KVal
  | .atom i  => [KVal.atom i]
  | .vec v   => v.toList.map KVal.atom
  | .fatom f => [KVal.fatom f]
  | .fvec v  => v.toList.map KVal.fatom
  | .box l   => l
  | .str s   => [KVal.str s]
  | .fn f    => [KVal.fn f]

private def fromList : List KVal → KVal
  | []  => KVal.box []
  | [KVal.atom i] => KVal.atom i
  | [KVal.fatom f] => KVal.fatom f
  | l   =>
    match l.mapM (fun v => match v with | KVal.atom i => some i | _ => none) with
    | some ints => KVal.vec ints.toArray
    | none =>
      match l.mapM (fun v => match v with | KVal.fatom f => some f | _ => none) with
      | some floats => KVal.fvec floats.toArray
      | none => KVal.box l

def join (x y : KVal) : Except KError KVal :=
  match x, y with
  | .str a, .str b => .ok $ .str (a ++ b)
  | _, _ => .ok $ fromList $ toList x ++ toList y

def iota_core (n : ℕ) : KVec := Array.range n |>.map Int.ofNat

def iota (x : KVal) : Except KError KVal :=
  match x with
  | .atom i =>
    if i < 0 then
      .error { kind := .domain, message := s!"'!' (iota) requires a non-negative integer. You provided {i}." }
    else
      let n : ℕ := i.toNat
      .ok (.vec $ iota_core n)

  | .vec v =>
      let dims := v.toList
      if dims.any (· < 0) then
        .error { kind := .domain, message := "'!' (iota) requires all non-negative integers" }
      else
        let natDims := (dims.map Int.toNat).toArray
        -- let vDims : Vector Nat natDims.size := ⟨natDims, rfl⟩
        let total := natDims.foldl (· * ·) 1
        let rows := (List.finRange natDims.size).map fun (i : Fin natDims.size) =>
          let stride := ((natDims.toList).drop (i.val + 1)).foldl (· * ·) 1
          let row : KVec := Array.ofFn (fun (j : Fin total) =>
            Int.ofNat ((j.val / stride) % natDims[i]))
          KVal.vec row
        .ok $ .box rows

  | .box _ =>
      .error { kind := .type, message := "'!' (iota) not implemented for box values" }
  | .str _ =>
      .error { kind := .type, message := "'!' (iota) not supported on strings" }
  | .fn _ =>
      .error { kind := .type, message := "'!' (iota) not supported on functions" }
  | .fatom _ =>
      .error { kind := .type, message := "'!' (iota) not supported on floats" }
  | .fvec _ =>
      .error { kind := .type, message := "'!' (iota) not supported on float vectors" }

/-! ### Division `%` -/

private def toFloat : KVal → Option Float
  | .atom i  => some (Float.ofInt i)
  | .fatom f => some f
  | _        => none

private def kDiv (x y : Float) : Float := x / y

private def kRecip (x : Float) : Float :=
  kDiv 1.0 x

private def div_vectors_core (v1 v2 : Array Float) : Array Float :=
  v1.zipWith (kDiv) v2

private def toFloatArray : KVal → Option (Array Float)
  | .vec v  => some (v.map Float.ofInt)
  | .fvec v => some v
  | _       => none

def kdiv (a b : KVal) : Except KError KVal :=
  match toFloat a, toFloat b with
  | some x, some y => .ok (.fatom (kDiv x y))
  | _, _ =>
    let va := toFloatArray a
    let vb := toFloatArray b
    match va, vb with
    | some v1, some v2 =>
      if v1.size = v2.size then
        .ok (.fvec (div_vectors_core v1 v2))
      else
        .error { kind := .length, message := s!"Cannot divide vector of length {v1.size} by vector of length {v2.size}" }
    | some v, none =>
      match toFloat b with
      | some y => .ok (.fvec (v.map (kDiv · y)))
      | none => .error { kind := .type, message := "'%' not supported between these types" }
    | none, some v =>
      match toFloat a with
      | some x => .ok (.fvec (v.map (kDiv x ·)))
      | none => .error { kind := .type, message := "'%' not supported between these types" }
    | none, none =>
      match a, b with
      | .box _, _ | _, .box _ => .error { kind := .type, message := "'%' not yet implemented for box values" }
      | .str _, _ | _, .str _ => .error { kind := .type, message := "'%' not supported on strings" }
      | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'%' not supported on functions" }
      | _, _ => .error { kind := .type, message := "'%' not supported between these types" }

def recip (x : KVal) : Except KError KVal :=
  match x with
  | .atom i  => .ok (.fatom (kRecip (Float.ofInt i)))
  | .fatom f => .ok (.fatom (kRecip f))
  | .vec v   => .ok (.fvec (v.map (fun i => kRecip (Float.ofInt i))))
  | .fvec v  => .ok (.fvec (v.map kRecip))
  | .box _   => .error { kind := .type, message := "'%' (reciprocal) not yet implemented for box values" }
  | .str _   => .error { kind := .type, message := "'%' (reciprocal) not supported on strings" }
  | .fn _    => .error { kind := .type, message := "'%' (reciprocal) not supported on functions" }
