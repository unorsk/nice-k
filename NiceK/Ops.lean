import NiceK.Types

def add_vectors_core {n : ℕ} (v1 : KVec n) (v2 : KVec n) : KVec n :=
  Vector.add v1 v2

def add (a b : KVal) : KResult KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok (.atom (x + y))

  | .vec n v1, .vec m v2 =>
      if h : n = m then
        let v2_cast : KVec n := h ▸ v2
        .ok (.vec n (add_vectors_core v1 v2_cast))
      else
        .error s!"Length Error: Cannot add vector of length {n} to vector of length {m}"

  | .atom x, .vec n v =>
      let scalar_vec := Vector.replicate n x
      .ok (.vec n (add_vectors_core scalar_vec v))

  | .vec n v, .atom y =>
      let scalar_vec := Vector.replicate n y
      .ok (.vec n (add_vectors_core v scalar_vec))

  | .generic _, _ => .error "Type Error: '+' not yet implemented for generic values"
  | _, .generic _ => .error "Type Error: '+' not yet implemented for generic values"

def iota_core (n : ℕ) : KVec n := Vector.ofFn (fun i => i.val)

def iota (x : KVal) : KResult KVal :=
  match x with
  | .atom i =>
    if i < 0 then
      .error s!"Domain Error: '!' (iota) requires a non-negative integer. You provided {i}."
    else
      let n : ℕ := i.toNat
      .ok (.vec n (iota_core n))

  | .vec n _v =>
      .error s!"Type Error: '!' (iota) not yet implemented for vectors. Input rank: 1, Shape: {n}"

  | .generic _ =>
      .error "Type Error: '!' (iota) not implemented for generic values"
