import NiceK.Types
import NiceK.AST
import Lean.Data.Parsec

def skipWs : Parsec Unit := do
  let _ ← many (satisfy fun c => c == ' ' || c == '\t' || c == '\n')
  return ()

/-- Parse a standard integer. Handles negative numbers. -/
def pInt : Parsec Int := do
  let s ← optional (pchar '-')
  let cs ← many1 digit
  let str := String.mk cs.toList
  let val := str.toInt!
  match s with
  | some _ => return -val
  | none   => return val

/-- Parse a KVal (currently just scalar integers). -/
def pVal : Parsec KExpr := do
  let i ← pInt
  return .val (.atom i)

/-- Parse a Verb (primitive function). -/
def pVerb : Parsec String := do
  -- We satisfy any char that is a known verb
  let c ← satisfy (fun c => c == '+' || c == '!' || c == '-' || c == '*')
  return c.toString

-- Forward declaration needed for recursive parsing
partial def pExpr : Parsec KExpr := do
  skipWs
  -- 1. Parse the "Left" term (Noun)
  let left ← pVal <|> (pchar '(' *> skipWs *> pExpr <* skipWs <* pchar ')')

  skipWs

  -- 2. Look ahead: Is there a Verb following this Noun?
  -- If yes, it's a Dyadic application.
  -- Note: This is a simplification. Real K parsing is hairier, but this works for basic math.
  (do
    let op ← pVerb
    skipWs
    let right ← pExpr -- Recurse Right (Right Associativity)
    return .dyadic op left right
  )
  <|>
  -- If no verb follows, it might be a Monadic verb acting on the rest?
  -- Actually, in strict structure:
  -- If we see a Noun, we stop unless there is an operator.
  -- If we see an Operator first, it is Monadic.
  return left

/-- Entry point for Monadic verbs at the start of line (e.g., !5) -/
partial def pLine : Parsec KExpr := do
  skipWs
  (do
    let op ← pVerb
    skipWs
    let right ← pExpr -- Recurse Right
    return .monadic op right
  )
  <|> pExpr

def parse (s : String) : KResult KExpr :=
  match pLine.run s with
  | .ok val => .ok val
  | .error e => .error s!"Parse Error: {e}"
