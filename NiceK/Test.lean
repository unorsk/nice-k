import NiceK.Primitives
import NiceK.Parser
import NiceK.Eval

/-! ## Test infrastructure

Tests use `#guard` — a compile-time check that fails the build if
the expression evaluates to `false`.  No IO, no runtime output. -/

/-- Parse and evaluate a K expression, returning the result as a string. -/
private def testEval (input : String) : String :=
  match parse input with
  | .error e => s!"ERROR: {e}"
  | .ok ast =>
    match evalIn [] ast with
    | .ok val => toString val
    | .error e => s!"ERROR: {e}"

/-- Parse and evaluate, returning both the result and final environment. -/
private def testEvalEnv (input : String) : String :=
  match parse input with
  | .error e => s!"ERROR: {e}"
  | .ok ast =>
    match evalWithEnv [] ast with
    | .ok (val, env) =>
      let envStr := env.reverse.map (fun (k, v) => s!"{k}={v}")
      s!"{val} env=[{String.intercalate ", " envStr}]"
    | .error e => s!"ERROR: {e}"

/-! ### Basics -/
section Basics
  #guard testEval "5"     == "5"
  #guard testEval "#1"    == "1"
  #guard testEval "!5"    == "[0, 1, 2, 3, 4]"
  #guard testEval "2 + 3" == "5"
end Basics

/-! ### Monadic verbs bind tightly -/
section MonadicBinding
  #guard testEval "!2 + 3"      == "[3, 4]"        -- (!2)+3
  #guard testEval "#1 + 2"      == "3"              -- (#1)+2
  #guard testEval "2 + !3"      == "[2, 3, 4]"      -- 2+(!3)
  #guard testEval "10 + 2 + !3" == "[12, 13, 14]"   -- 10+(2+(!3))
end MonadicBinding

/-! ### Right-to-left / right-associative -/
section RightToLeft
  #guard testEval "1 + #1"    == "2"
  #guard testEval "1 + #(1 1)" == "3"
end RightToLeft

/-! ### Subtraction (lexer: `-` is context-sensitive) -/
section Subtraction
  #guard testEval "5 - 3"        == "2"
  #guard testEval "5-3"          == "2"
  #guard testEval "1 -2"         == "[1, -2]"        -- vector literal
  #guard testEval "-3"           == "-3"              -- negative literal
  #guard testEval "10 - 2 - !3"  == "[8, 9, 10]"     -- 10-(2-(0 1 2))
end Subtraction

/-! ### Negate (monadic `-`) -/
section Negate
  #guard testEval "- 3"  == "-3"
  #guard testEval "--3"  == "3"     -- negate(negate(-3))... -(-3) = 3
end Negate

/-! ### Each `'` adverb -/
section EachAdverb
  -- Positive
  #guard testEval "1+'1 1"          == "[2, 2]"
  #guard testEval "1+'(1 2)"        == "[2, 3]"
  #guard testEval "(1 1 2)+'1 1 2"  == "[2, 2, 4]"

  -- Errors
  #guard (testEval "1+'1").startsWith           "ERROR: Type Error"
  #guard (testEval "(1 1 2)+'1 1").startsWith   "ERROR: Length Error"
end EachAdverb

/-! ### Assignment `:` -/
section Assignment
  #guard testEval "a:5"            == "5"
  #guard testEval "a:5; a"         == "5"
  #guard testEval "a:5; a+1"      == "6"
  #guard testEval "3+a:5"          == "8"          -- assignment returns value
  #guard testEval "a:1; b:a+2; b"  == "3"          -- chained
  #guard testEval "a:!3; a"        == "[0, 1, 2]"  -- assign vector

  -- Environment tracking
  #guard testEvalEnv "a:5"        == "5 env=[a=5]"
  #guard testEvalEnv "a:1; b:a+2" == "3 env=[a=1, b=3]"
end Assignment

/-! ### Semicolons `;` -/
section Semicolons
  #guard testEval "1;2;3"      == "3"
  #guard testEval "a:2+3;6+7"  == "13"
end Semicolons

/-! ### Error cases -/
section Errors
  -- Domain
  #guard (testEval "! -1").startsWith "ERROR: Domain Error"

  -- Length
  #guard (testEval "!2 + 3 + (2 + (!3))").startsWith "ERROR: Length Error"

  -- Syntax: assignment LHS
  #guard (testEval "5:3").startsWith     "ERROR: Syntax Error"
  #guard (testEval "(1+2):3").startsWith "ERROR: Syntax Error"

  -- Syntax: semicolons
  #guard (testEval "1;;2").startsWith "ERROR: Syntax Error"
  #guard (testEval ";1").startsWith   "ERROR: Syntax Error"
  #guard (testEval "1;").startsWith   "ERROR: Syntax Error"

  -- Parse: parens
  #guard (testEval "(1+2").startsWith "ERROR: Parse Error"
  #guard (testEval "1+2)").startsWith "ERROR: Parse Error"

  -- Nested parens OK
  #guard testEval "((1+2))" == "3"
end Errors

/-! ### Primitive-level tests -/
section Primitives
  private def showResult (r : Except KError KVal) : String :=
    match r with
    | .ok v => toString v
    | .error e => s!"ERROR: {e}"

  #guard showResult (iota (.atom 5))          == "[0, 1, 2, 3, 4]"
  #guard (iota (.atom (-5))).isOk             == false
  #guard (iota (.atom (-1))).isOk             == false
  #guard showResult (add (.vec #[1,2,3]) (.vec #[1,2,3])) == "[2, 4, 6]"
  #guard (add (.vec #[1,2,3]) (.vec #[1,2,3,4])).isOk     == false
end Primitives
