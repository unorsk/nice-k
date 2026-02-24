import NiceK.Types

def add_vectors_core {n : ℕ} (v1 : KVec n) (v2 : KVec n) : KVec n :=
  Vector.add v1 v2

def sub_vectors_core {n : ℕ} (v1 : KVec n) (v2 : KVec n) : KVec n :=
  Vector.zipWith (· - ·) v1 v2

def add (a b : KVal) : Except KError KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok (.atom (x + y))

  | .vec n v1, .vec m v2 =>
      if h : n = m then
        let v2_cast : KVec n := h ▸ v2
        .ok (.vec n (add_vectors_core v1 v2_cast))
      else
        .error { kind := .length, message := s!"Cannot add vector of length {n} to vector of length {m}" }

  | .atom x, .vec n v =>
      let scalar_vec := Vector.replicate n x
      .ok (.vec n (add_vectors_core scalar_vec v))

  | .vec n v, .atom y =>
      let scalar_vec := Vector.replicate n y
      .ok (.vec n (add_vectors_core v scalar_vec))

  | .generic _, _ => .error { kind := .type, message := "'+' not yet implemented for generic values" }
  | _, .generic _ => .error { kind := .type, message := "'+' not yet implemented for generic values" }

def negate (x : KVal) : Except KError KVal :=
  match x with
  | .atom i     => .ok (.atom (-i))
  | .vec n v    => .ok (.vec n (Vector.map (- ·) v))
  | .generic _  => .error { kind := .type, message := "'-' (negate) not yet implemented for generic values" }

def sub (a b : KVal) : Except KError KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok (.atom (x - y))

  | .vec n v1, .vec m v2 =>
      if h : n = m then
        let v2_cast : KVec n := h ▸ v2
        .ok (.vec n (sub_vectors_core v1 v2_cast))
      else
        .error { kind := .length, message := s!"Cannot subtract vector of length {m} from vector of length {n}" }

  | .atom x, .vec n v =>
      let scalar_vec := Vector.replicate n x
      .ok (.vec n (sub_vectors_core scalar_vec v))

  | .vec n v, .atom y =>
      let scalar_vec := Vector.replicate n y
      .ok (.vec n (sub_vectors_core v scalar_vec))

  | .generic _, _ => .error { kind := .type, message := "'-' not yet implemented for generic values" }
  | _, .generic _ => .error { kind := .type, message := "'-' not yet implemented for generic values" }

def iota_core (n : ℕ) : KVec n := Vector.ofFn (fun i => i.val)

def iota (x : KVal) : Except KError KVal :=
  match x with
  | .atom i =>
    if i < 0 then
      .error { kind := .domain, message := s!"'!' (iota) requires a non-negative integer. You provided {i}." }
    else
      let n : ℕ := i.toNat
      .ok (.vec n (iota_core n))

  | .vec n v =>
      let dims := v.toList
      if dims.any (· < 0) then
        .error { kind := .domain, message := "'!' (iota) requires all non-negative integers" }
      else
        let natDims := (dims.map Int.toNat).toArray
        let vDims : Vector Nat natDims.size := ⟨natDims, rfl⟩
        let total := natDims.foldl (· * ·) 1
        let rows := (List.finRange vDims.size).map fun (i : Fin vDims.size) =>
          let stride := ((natDims.toList).drop (i.val + 1)).foldl (· * ·) 1
          let row : Vector Int total := Vector.ofFn (fun (j : Fin total) =>
            Int.ofNat ((j.val / stride) % vDims[i]))
          KVal.vec total row
        .ok (.generic rows)

  | .generic _ =>
      .error { kind := .type, message := "'!' (iota) not implemented for generic values" }
