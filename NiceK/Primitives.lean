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

  | .box _, _ | _, .box _ => .error { kind := .type, message := "'+' not yet implemented for box values" }
  | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'+' not supported on functions" }

def negate (x : KVal) : Except KError KVal :=
  match x with
  | .atom i     => .ok (.atom (-i))
  | .vec v    => .ok (.vec (Array.map (- ·) v))
  | .box _  => .error { kind := .type, message := "'-' (negate) not yet implemented for box values" }
  | .fn _   => .error { kind := .type, message := "'-' (negate) not supported on functions" }

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

  | .box _, _ | _, .box _ => .error { kind := .type, message := "'-' not yet implemented for box values" }
  | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'-' not supported on functions" }

def mul_vectors_core (v1 : KVec) (v2 : KVec) : KVec :=
  v1.zipWith (· * ·) v2

def mul (a b : KVal) : Except KError KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok (.atom (x * y))

  | .vec v1, .vec v2 =>
      if v1.size = v2.size then
        .ok (.vec (mul_vectors_core v1 v2))
      else
        .error { kind := .length, message := s!"Cannot multiply vector of length {v1.size} by vector of length {v2.size}" }

  | .atom x, .vec v =>
      let scalar_vec := Array.replicate v.size x
      .ok (.vec $ mul_vectors_core scalar_vec v)

  | .vec v, .atom y =>
      let scalar_vec := Array.replicate v.size y
      .ok (.vec $ mul_vectors_core v scalar_vec)

  | .box _, _ | _, .box _ => .error { kind := .type, message := "'*' not yet implemented for box values" }
  | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'*' not supported on functions" }

def first (x : KVal) : Except KError KVal :=
  match x with
  | .atom i  => .ok (.atom i)
  | .vec v   =>
    if v.size == 0 then
      .error { kind := .domain, message := "'*' (first) requires a non-empty list" }
    else
      .ok (.atom v[0]!)
  | .box l   =>
    match l with
    | []     => .error { kind := .domain, message := "'*' (first) requires a non-empty list" }
    | a :: _ => .ok a
  | .fn f    => .ok (.fn f)

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
        .ok (.box rows)

  | .box _ =>
      .error { kind := .type, message := "'!' (iota) not implemented for box values" }
  | .fn _ =>
      .error { kind := .type, message := "'!' (iota) not supported on functions" }
