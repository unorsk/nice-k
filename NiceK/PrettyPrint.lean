import NiceK.Types

class KDisplay (α : Type) where
  display : α → String

partial def displayKVal : KVal → String
  | .atom i  => toString i
  | .fatom f => floatToKString f
  | .str s   => s
  | .vec v   =>
    if v.size == 0 then
      "()"
    else
      " ".intercalate (v.toList.map toString)
  | .fvec v  =>
    if v.size == 0 then
      "()"
    else
      " ".intercalate (v.toList.map floatToKString)
  | .box xs  =>
    match xs with
    | [] => "()"
    | _  => "\n".intercalate (xs.map displayKVal)
  | .fn f    => toString f

instance : KDisplay KVal where
  display := displayKVal

def kDisplay [KDisplay α] (a : α) : String :=
  KDisplay.display a
