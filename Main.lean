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

def main : IO Unit := do
  run_script "5"
  run_script "!5"
  run_script "2 + 3"
  run_script "2 + !3"        -- 2 + (0 1 2) -> 2 3 4
  run_script "10 + 2 + !3"   -- 10 + (2 + (!3))
  run_script "! -1"          -- Runtime error check
