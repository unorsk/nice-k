import NiceK
import NiceK.Parser

def run_script (input : String) : IO Unit := do
  IO.print s!"Input: {input}  =>  "
  IO.println $  match parse input with
  | .error e => toString e
  | .ok ast =>
      match eval [] ast with
      | .ok val => toString val
      | .error e => toString e

#eval run_script "!2 3"
#eval run_script "1 + #1"
#eval run_script "1 + #(1 1)"
#eval run_script "#1"
#eval run_script "5"
#eval run_script "5"
#eval run_script "!5"
#eval run_script "2 + 3"
#eval run_script "!2 + 3 + (2 + (!3))"
#eval run_script "!2 + 3 + (2 + !3)"
#eval run_script "!2 + 3 + 2 + !3"
#eval run_script "!2 + 3 + 2 + !3"
#eval run_script "2 + 3 + 2 + !3"
#eval run_script "!2 + 3 + 2 + 3"
#eval run_script "2 + !3"        -- 2 + (0 1 2) -> 2 3 4
#eval run_script "10 + 2 + !3"   -- 10 + (2 + (!3))
#eval run_script "! -1"          -- Runtime error check


def main : IO Unit := do
  IO.println "Hello"
