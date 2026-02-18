import NiceK.Ops

def run_test (name : String) (res : Except KError KVal) : IO Unit := do
  match res with
  | .ok v => IO.println s!"ok: {name} : {v}"
  | .error e => IO.println s!"error: {name} : {e}"

#eval run_test "Test 1 (!-5)" (iota (.atom (-5)))

#eval run_test "Test 1 (!5)" (iota (.atom 5))

#eval run_test "Test 2 (!-1)" (iota (.atom (-1)))

#eval run_test "Test 3 (!vector)" (iota (.vec 3 (Vector.mk #[1, 2, 3] rfl)))

#eval run_test "Test 4" (add (.vec 3 (Vector.mk #[1, 2, 3] rfl)) (.vec 3 (Vector.mk #[1, 2, 3] rfl)))
#eval run_test "Test 4" (add (.vec 3 (Vector.mk #[1, 2, 3] rfl)) (.vec 4 (Vector.mk #[1, 2, 3, 4] rfl)))
