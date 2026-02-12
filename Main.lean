import NiceK
import NiceK.Parser

def run_script (input : String) : IO Unit := do
  IO.print s!"Input: {input}  =>  "
  match parse input with
  | .error e => IO.println e
  | .ok ast =>
      -- Optional: Print AST to see structure
      -- IO.print s!"[AST: {ast}] => "
      match eval ast with
      | .ok val => IO.println val
      | .error e => IO.println e

def main : IO Unit :=
  run_script "5"
  run_script "!5"
  run_script "2 + 3"
  run_script "2 + !3"        -- Should be 2 + (0 1 2) -> 2 3 4
  run_script "10 + 2 + !3"   -- Right associative check: 10 + (2 + (!3))
  run_script "! -1"          -- Runtime error check
  run_script "2 + !2"        -- Vector math
