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
  #eval testEval "+" -- should be +3^!rank
  -- #eval testEval "+3" -- should be +3^!rank
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

/-! ### Lambda tests -/
section Lambdas
  -- Explicit params
  #guard testEval "{[x] x+1}[3]"           == "4"
  #guard testEval "{[x;y] x+y}[3;4]"       == "7"

  -- Implicit params (x, y, z)
  #guard testEval "{x+1}[3]"               == "4"
  #guard testEval "{x+y}[3;4]"             == "7"

  -- Nullary
  #guard testEval "{[] 42}[]"               == "42"

  -- Functions are first-class values
  #guard testEval "f:{x+1}; f[3]"          == "4"
  #guard testEval "f:{[x;y] x+y}; f[3;4]" == "7"

  -- Closures: capture environment at definition time
  #guard testEval "a:10; f:{[] a}; f[]"    == "10"
  #guard testEval "a:10; f:{x+a}; f[5]"   == "15"

  -- Nested lambdas (closure captures outer param)
  #guard testEval "{[x] {[y] x+y}}[3][4]"  == "7"

  -- Lambda in expressions
  #guard testEval "1+{x+1}[3]"             == "5"

  -- Multi-expression body
  #guard testEval "{[x] a:x+1; a+2}[10]"   == "13"

  -- Lambda with z (third implicit param)
  #guard testEval "{x+y+z}[1;2;3]"         == "6"

  -- Lambda returning a lambda (higher-order)
  #guard testEval "add:{[x] {[y] x+y}}; add[10][5]" == "15"

  -- Closure captures value, not reference (capture-by-value)
  #guard testEval "a:1; f:{[] a}; a:2; f[]"  == "1"

  -- Lambda applied to vectors
  #guard testEval "{x+1}[3 4 5]"            == "[4, 5, 6]"

  -- Chained application
  #guard testEval "{[x] {[y] {[z] x+y+z}}}[1][2][3]" == "6"

  -- Error: wrong arity
  #guard (testEval "{[x;y] x+y}[1]").startsWith   "ERROR:"
  #guard (testEval "{[x] x}[1;2]").startsWith      "ERROR:"

  -- Error: calling a non-function
  #guard (testEval "5[3]").startsWith              "ERROR:"
end Lambdas

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
