import NiceK
import NiceK.Parser

def runLine (env : KEnv) (line : String) : IO KEnv := do
  match parse line with
  | .error e =>
    IO.eprintln (toString e)
    return env
  | .ok ast =>
    match evalWithEnv env ast with
    | .error e =>
      IO.eprintln (toString e)
      return env
    | .ok (val, env') =>
      IO.println (toString val)
      return env'

def repl : IO Unit := do
  let mut env : KEnv := []
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  while true do
    stdout.putStr " "
    stdout.flush
    let line ← stdin.getLine
    if line.isEmpty then break  -- EOF
    let trimmed := line.trim
    if trimmed.isEmpty then continue
    if trimmed == "\\\\" then break
    env ← runLine env trimmed

def script : IO Unit := do
  let stdin ← IO.getStdin
  let mut env : KEnv := []
  while true do
    let line ← stdin.getLine
    if line.isEmpty then break
    let trimmed := line.trim
    if trimmed.isEmpty then continue
    env ← runLine env trimmed

def main (args : List String) : IO Unit := do
  if args.contains "repl" then
    repl
  else
    script
