import NiceK.Primitives
import NiceK.Parser
import NiceK.Eval

def run_test (name : String) (res : Except KError KVal) : IO Unit := do
  match res with
  | .ok v => IO.println s!"ok: {name} : {v}"
  | .error e => IO.println s!"error: {name} : {e}"

def run_e2e (input : String) : IO Unit := do
  IO.print s!"  {input}  =>  "
  IO.println $ match parse input with
  | .error e => s!"ERROR: {e}"
  | .ok ast =>
    match eval [] ast with
    | .ok val => s!"OK: {val}"
    | .error e => s!"ERROR: {e}"

-- ===== Ops-level tests =====
#eval run_test "Test 1 (!-5)" (iota (.atom (-5)))
#eval run_test "Test 1 (!5)" (iota (.atom 5))
#eval run_test "Test 2 (!-1)" (iota (.atom (-1)))
#eval run_test "Test 3 (!vector)" (iota (.vec #[1, 2, 3]))
#eval run_test "Test 4" (add (.vec #[1, 2, 3]) (.vec #[1, 2, 3]))
#eval run_test "Test 4" (add (.vec #[1, 2, 3]) (.vec #[1, 2, 3, 4]))

-- ===== Each ' adverb tests =====
#eval IO.println "\n--- Each ' adverb: negative examples (expect errors) ---"
#eval run_e2e "1+'1"            -- Type error: each requires at least one list
#eval run_e2e "(1 1 2)+'1 1"   -- Length error: 3 vs 2

#eval IO.println "\n--- Each ' adverb: positive examples ---"
#eval run_e2e "1+'1 1"         -- => 2 2
#eval run_e2e "1+'(1 2)"       -- => 2 3
#eval run_e2e "(1 1 2)+'1 1 2" -- => 2 2 4
