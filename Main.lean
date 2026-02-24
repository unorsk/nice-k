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

-- === Basics ===
#eval run_script "5"
#eval run_script "#1"            -- count(1) = 1
#eval run_script "!5"            -- iota 5 = 0 1 2 3 4
#eval run_script "2 + 3"         -- 5

-- === Monadic verbs bind tightly (parser fix) ===
#eval run_script "!2 + 3"        -- (!2)+3 = (0 1)+3 = 3 4
#eval run_script "#1 + 2"        -- (#1)+2 = 1+2 = 3
#eval run_script "2 + !3"        -- 2+(!(3)) = 2+(0 1 2) = 2 3 4
#eval run_script "10 + 2 + !3"   -- 10+(2+(!3)) = 10+(2 3 4) = 12 13 14

-- === Right-to-left / right-associative ===
#eval run_script "!2 3"          -- !(2 3) = multi-dim iota
#eval run_script "1 + #1"        -- 1+(#1) = 1+1 = 2
#eval run_script "1 + #(1 1)"    -- 1+(#(1 1)) = 1+2 = 3

-- === Subtraction (lexer fix: `-` is context-sensitive) ===
#eval run_script "5 - 3"         -- 2
#eval run_script "5-3"           -- 2  (no space: dyadic subtract)
#eval run_script "1 -2"          -- vector (1 -2)
#eval run_script "-3"            -- -3  (negative literal)
#eval run_script "10 - 2 - !3"   -- 10-(2-(0 1 2)) = 10-(2 1 0) = 8 9 10

-- === Negate (monadic -) ===
#eval run_script "- 3"           -- negate 3 = -3
#eval run_script "--3"           -- negate(negate 3)... wait, --3 = negate of -3 = 3

-- === Edge cases ===
#eval run_script "! -1"          -- domain error (iota of -1)
#eval run_script "!2 + 3 + (2 + (!3))"  -- (!2)+(3+(2+(!3))) = (0 1)+(3+(2 3 4)) = (0 1)+(5 6 7) = length error


def main : IO Unit := do
  IO.println "Hello"
