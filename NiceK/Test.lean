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
    match evalIn [] ast with
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

-- ===== Assignment : tests =====
#eval IO.println "\n--- Assignment : ---"
#eval run_e2e "a:5"             -- => 5 (assignment returns assigned value)
#eval run_e2e "a:5; a"          -- => 5 (variable lookup after assignment)
#eval run_e2e "a:5; a+1"       -- => 6
#eval run_e2e "3+a:5"           -- => 8 (assignment value participates in expression)
#eval run_e2e "a:1; b:a+2; b"  -- => 3 (chained assignments)
#eval run_e2e "a:!3; a"        -- => [0, 1, 2] (assign vector)

-- ===== Semicolons ; tests =====
#eval IO.println "\n--- Semicolons ; ---"
#eval run_e2e "1;2;3"           -- => 3 (last value returned)
#eval run_e2e "a:2+3;6+7"     -- => 13 (a=5, returns 13)

-- ===== Semicolons ; error tests =====
#eval IO.println "\n--- Semicolons ; error tests ---"
#eval run_e2e "1;;2"            -- syntax error
#eval run_e2e ";1"              -- syntax error
#eval run_e2e "1;"              -- syntax error

-- ===== Assignment : error tests =====
#eval IO.println "\n--- Assignment : error tests ---"
#eval run_e2e "5:3"             -- syntax error (LHS must be variable)
#eval run_e2e "(1+2):3"         -- syntax error

-- ===== Parser: paren / nesting error tests =====
#eval IO.println "\n--- Parser error tests ---"
#eval run_e2e "(1+2"            -- Unmatched '('
#eval run_e2e "1+2)"            -- Unmatched ')'
#eval run_e2e "((1+2))"         -- Nested parens OK => 3
