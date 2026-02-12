import NiceK.Types
import NiceK.AST
import Std.Internal.Parsec
import Std.Internal.Parsec.String

open Std.Internal.Parsec.String
open Std.Internal.Parsec

def skipWs : Parser Unit := do
  let _ ← many (satisfy fun c => c == ' ' || c == '\t' || c == '\n')
  return ()

def pInt : Parser Int := do
  let s ← optional (pchar '-')
  let cs ← many1 digit
  let str := String.ofList cs.toList
  let val := str.toInt!
  match s with
  | some _ => return -val
  | none   => return val

def pVal : Parser KExpr := do
  let i ← pInt
  return .val (.atom i)

def pVerb : Parser String := do
  let c ← satisfy (fun c => c == '+' || c == '!' || c == '-' || c == '*')
  return c.toString

partial def pExpr : Parser KExpr := do
  skipWs
  let left ← pVal
    <|> (pchar '(' *> skipWs *> pExpr <* skipWs <* pchar ')')
    <|> (do let op ← pVerb; skipWs; let right ← pExpr; return .monadic op right)

  skipWs

  -- look ahead if there's a verb, oversimplified, fix later
  (do
    let op ← pVerb
    skipWs
    let right ← pExpr -- Recurse Right (Right Associativity)
    return .dyadic op left right
  )
  <|>
  return left

partial def pLine : Parser KExpr := do
  skipWs
  (do
    let op ← pVerb
    skipWs
    let right ← pExpr -- Recurse Right
    return .monadic op right
  )
  <|> pExpr

def parse (s : String) : KResult KExpr :=
  match Parser.run pLine s with
  | .ok val => .ok val
  | .error e => .error s!"Parse Error: {e}"
