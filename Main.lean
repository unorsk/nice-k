import NiceK

notation "ℕ" => Nat

def KVec (n : ℕ) := Vector Int n

mutual
  inductive KVal where
    | atom : Int → KVal
    | vec (n : ℕ) : KVec n → KVal
    | generic (n : ℕ) : KValVec n → KVal

  inductive KValVec : ℕ → Type where
    | nil : KValVec 0
    | cons : KVal → KValVec n → KValVec (n + 1)
end

mutual
  def KVal.toString : KVal → String
    | .atom i => s!"{i}"
    | .vec _n v => s!"{v.toList}"
    | .generic _n vs => s!"({KValVec.toString vs})"

  def KValVec.toString : KValVec n → String
    | .nil => ""
    | .cons v .nil => KVal.toString v
    | .cons v vs => s!"{KVal.toString v}; {KValVec.toString vs}"
end

instance : ToString KVal := ⟨KVal.toString⟩
instance : ToString (KValVec n) := ⟨KValVec.toString⟩

inductive KResult (α : Type) where
  | ok : α → KResult α
  | error : String → KResult α

def add_vectors_core {n : ℕ} (v1 : KVec n) (v2 : KVec n) : KVec n :=
  Vector.add v1 v2

def add (a b : KVal) : KResult KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok (.atom (x + y))

  | .vec n v1, .vec m v2 =>
      if h : n = m then
        -- CRITICAL: 'h' is a PROOF that n = m.
        -- We cast v2 to type 'KVec n' using the proof 'h'.
        let v2_cast : KVec n := h ▸ v2
        .ok (.vec n (add_vectors_core v1 v2_cast))
      else
        .error s!"Length Error: Cannot add vector of length {n} to vector of length {m}"

  -- Case 3: Atom + Vector (Scalar Extension)
  | .atom x, .vec n v =>
      let scalar_vec := Vector.replicate n x
      .ok (.vec n (add_vectors_core scalar_vec v))

  -- Case 4: Vector + Atom (Commutative)
  | .vec n v, .atom y =>
      let scalar_vec := Vector.replicate n y
      .ok (.vec n (add_vectors_core v scalar_vec))

  -- Generic cases (not yet implemented)
  | .generic _ _, _ => .error "Type Error: '+' not yet implemented for generic values"
  | _, .generic _ _ => .error "Type Error: '+' not yet implemented for generic values"

def iota_core (n : ℕ) : KVec n := Vector.ofFn (fun i => i.val)

def iota (x : KVal) : KResult KVal :=
  match x with
  | .atom i =>
    -- Some of K dialects (most?) allow for negative numbers here
    -- OK
    -- !-4
    -- -4 -3 -2 -1
    if i < 0 then
      .error s!"Domain Error: '!' (iota) requires a non-negative integer. You provided {i}."
    else
      let n : ℕ := i.toNat

      .ok (.vec n (iota_core n))

  | .vec n _v =>
      -- Nice Error #2: Rank/Type Error
      -- In K, !vector is actually valid (odometer/permutation),
      -- but for our subset, we'll mark it as unimplemented or error.
      .error s!"Type Error: '!' (iota) not yet implemented for vectors. Input rank: 1, Shape: {n}"

  | .generic _ _ =>
      .error "Type Error: '!' (iota) not implemented for generic values"

def run_test (name : String) (res : KResult KVal) : IO Unit := do
  match res with
  | .ok v => IO.println s!"ok: {name} : {v}"
  | .error e => IO.println s!"error: {name} : {e}"



#eval run_test "Test 1 (!-5)" (iota (.atom (-5)))

#eval run_test "Test 1 (!5)" (iota (.atom 5))
-- Output: Test 1 (!5)  : [0, 1, 2, 3, 4]

#eval run_test "Test 2 (!-1)" (iota (.atom (-1)))
-- Output: Test 2 (!-1) : Domain Error: '!' (iota) requires a non-negative integer. You provided -1.

#eval run_test "Test 3 (!vector)" (iota (.vec 3 (Vector.mk #[1, 2, 3] rfl)))
-- Output: Test 3 (!vector) : Type Error: '!' (iota) not yet implemented for vectors. Input rank: 1, Shape: 3

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
