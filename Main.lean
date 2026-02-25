import NiceK
import NiceK.Parser

def run (input : String) : IO Unit := do
  IO.print s!"  {input}  =>  "
  IO.println $ match parse input with
  | .error e => toString e
  | .ok ast =>
      match evalIn [] ast with
      | .ok val => toString val
      | .error e => toString e

def main : IO Unit := do
  IO.println "Hello"
