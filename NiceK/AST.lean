import NiceK.Types
import Lean.Parser
import Init.Data.Repr

-- deriving instance Repr for KVal

inductive KExpr where
  | val : KVal → KExpr                     -- A raw value (number, list)
  | var : String → KExpr                   -- A variable name (e.g., x, y)
  | dyadic : String → KExpr → KExpr → KExpr -- Operator, Left, Right (e.g., 1 + 2)
  | monadic : String → KExpr → KExpr        -- Operator, Right (e.g., !5)
  -- deriving Repr

-- instance : ToString KExpr := ⟨fun e => s!"{repr e}"⟩
instance : ToString KExpr := ⟨fun _e => s!"e"⟩
