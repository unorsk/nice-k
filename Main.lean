import NiceK
import NiceK.Parser

def run_script (input : String) : IO Unit := do
  IO.print s!"Input: {input}  =>  "
  match parse input with
  | .error e => IO.println e
  | .ok ast =>
      match eval ast with
      | .ok val => IO.println val
      | .error e => IO.println e

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
