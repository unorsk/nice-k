import NiceK.Types

def add_vectors_core (v1 : KVec) (v2 : KVec) : KVec :=
  v1.zipWith (· + ·) v2

def sub_vectors_core (v1 : KVec) (v2 : KVec) : KVec :=
  v1.zipWith (· - ·) v2

def add (a b : KVal) : Except KError KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok (.atom (x + y))

  | .vec v1, .vec v2 =>
      if v1.size = v2.size then
        .ok (.vec (add_vectors_core v1 v2))
      else
        .error { kind := .length, message := s!"Cannot add vector of length {v1.size} to vector of length {v2.size}" }

  | .atom x, .vec v =>
      let scalar_vec := Array.replicate v.size x
      .ok (.vec $ add_vectors_core scalar_vec v)

  | .vec v, .atom y =>
      let scalar_vec := Array.replicate v.size y
      .ok (.vec $ add_vectors_core v scalar_vec)

  | .fatom _, _ | _, .fatom _ | .fvec _, _ | _, .fvec _ =>
      .error { kind := .type, message := "'+' not yet implemented for float values" }
  | .box _, _ | _, .box _ => .error { kind := .type, message := "'+' not yet implemented for box values" }
  | .str _, _ | _, .str _ => .error { kind := .type, message := "'+' not supported on strings" }
  | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'+' not supported on functions" }

def negate (x : KVal) : Except KError KVal :=
  match x with
  | .atom i  => .ok (.atom (-i))
  | .vec v   => .ok (.vec (Array.map (- ·) v))
  | .fatom f => .ok (.fatom (-f))
  | .fvec v  => .ok (.fvec (Array.map (- ·) v))
  | .box _   => .error { kind := .type, message := "'-' (negate) not yet implemented for box values" }
  | .str _   => .error { kind := .type, message := "'-' (negate) not supported on strings" }
  | .fn _    => .error { kind := .type, message := "'-' (negate) not supported on functions" }

def sub (a b : KVal) : Except KError KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok (.atom (x - y))

  | .vec v1, .vec v2 =>
      if v1.size = v2.size then
        .ok (.vec $ sub_vectors_core v1 v2)
      else
        .error { kind := .length, message := s!"Cannot subtract vector of length {v1.size} from vector of length {v2.size}" }

  | .atom x, .vec v =>
      let scalar_vec := Array.replicate v.size x
      .ok (.vec (sub_vectors_core scalar_vec v))

  | .vec v, .atom y =>
      let scalar_vec := Array.replicate v.size y
      .ok (.vec $ sub_vectors_core v scalar_vec)

  | .fatom _, _ | _, .fatom _ | .fvec _, _ | _, .fvec _ =>
      .error { kind := .type, message := "'-' not yet implemented for float values" }
  | .box _, _ | _, .box _ => .error { kind := .type, message := "'-' not yet implemented for box values" }
  | .str _, _ | _, .str _ => .error { kind := .type, message := "'-' not supported on strings" }
  | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'-' not supported on functions" }

def mul_vectors_core (v1 : KVec) (v2 : KVec) : KVec :=
  v1.zipWith (· * ·) v2

def mul (a b : KVal) : Except KError KVal :=
  match a, b with
  | .atom x, .atom y =>
      .ok $ .atom (x * y)

  | .vec v1, .vec v2 =>
      if v1.size = v2.size then
        .ok $ .vec (mul_vectors_core v1 v2)
      else
        .error { kind := .length, message := s!"Cannot multiply vector of length {v1.size} by vector of length {v2.size}" }

  | .atom x, .vec v =>
      let scalar_vec := Array.replicate v.size x
      .ok $ .vec $ mul_vectors_core scalar_vec v

  | .vec v, .atom y =>
      let scalar_vec := Array.replicate v.size y
      .ok $ .vec $ mul_vectors_core v scalar_vec

  | .fatom _, _ | _, .fatom _ | .fvec _, _ | _, .fvec _ =>
      .error { kind := .type, message := "'*' not yet implemented for float values" }
  | .box _, _ | _, .box _ => .error { kind := .type, message := "'*' not yet implemented for box values" }
  | .str _, _ | _, .str _ => .error { kind := .type, message := "'*' not supported on strings" }
  | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'*' not supported on functions" }

def first (x : KVal) : Except KError KVal :=
  match x with
  | .atom i  => .ok $ .atom i
  | .fatom f => .ok $ .fatom f
  | .vec v   =>
    if v.size == 0 then
      .error { kind := .domain, message := "'*' (first) requires a non-empty list" }
    else
      .ok $ .atom v[0]!
  | .fvec v  =>
    if v.size == 0 then
      .error { kind := .domain, message := "'*' (first) requires a non-empty list" }
    else
      .ok $ .fatom v[0]!
  | .box l   =>
    match l with
    | []     => .error { kind := .domain, message := "'*' (first) requires a non-empty list" }
    | a :: _ => .ok a
  | .str s   =>
    if s.isEmpty then
      .error { kind := .domain, message := "'*' (first) requires a non-empty string" }
    else
      .ok $ .str s.front.toString
  | .fn f    => .ok $ .fn f

def enlist (x : KVal) : KVal := .box [x]

private def toList : KVal → List KVal
  | .atom i  => [KVal.atom i]
  | .vec v   => v.toList.map KVal.atom
  | .fatom f => [KVal.fatom f]
  | .fvec v  => v.toList.map KVal.fatom
  | .box l   => l
  | .str s   => [KVal.str s]
  | .fn f    => [KVal.fn f]

private def fromList : List KVal → KVal
  | []  => KVal.box []
  | [KVal.atom i] => KVal.atom i
  | [KVal.fatom f] => KVal.fatom f
  | l   =>
    match l.mapM (fun v => match v with | KVal.atom i => some i | _ => none) with
    | some ints => KVal.vec ints.toArray
    | none =>
      match l.mapM (fun v => match v with | KVal.fatom f => some f | _ => none) with
      | some floats => KVal.fvec floats.toArray
      | none => KVal.box l

def join (x y : KVal) : Except KError KVal :=
  match x, y with
  | .str a, .str b => .ok $ .str (a ++ b)
  | _, _ => .ok $ fromList $ toList x ++ toList y

def iota_core (n : ℕ) : KVec := Array.range n |>.map Int.ofNat

def iota (x : KVal) : Except KError KVal :=
  match x with
  | .atom i =>
    if i < 0 then
      .error { kind := .domain, message := s!"'!' (iota) requires a non-negative integer. You provided {i}." }
    else
      let n : ℕ := i.toNat
      .ok (.vec $ iota_core n)

  | .vec v =>
      let dims := v.toList
      if dims.any (· < 0) then
        .error { kind := .domain, message := "'!' (iota) requires all non-negative integers" }
      else
        let natDims := (dims.map Int.toNat).toArray
        -- let vDims : Vector Nat natDims.size := ⟨natDims, rfl⟩
        let total := natDims.foldl (· * ·) 1
        let rows := (List.finRange natDims.size).map fun (i : Fin natDims.size) =>
          let stride := ((natDims.toList).drop (i.val + 1)).foldl (· * ·) 1
          let row : KVec := Array.ofFn (fun (j : Fin total) =>
            Int.ofNat ((j.val / stride) % natDims[i]))
          KVal.vec row
        .ok $ .box rows

  | .box _ =>
      .error { kind := .type, message := "'!' (iota) not implemented for box values" }
  | .str _ =>
      .error { kind := .type, message := "'!' (iota) not supported on strings" }
  | .fn _ =>
      .error { kind := .type, message := "'!' (iota) not supported on functions" }
  | .fatom _ =>
      .error { kind := .type, message := "'!' (iota) not supported on floats" }
  | .fvec _ =>
      .error { kind := .type, message := "'!' (iota) not supported on float vectors" }

/-! ### Division `%` -/

private def toFloat : KVal → Option Float
  | .atom i  => some (Float.ofInt i)
  | .fatom f => some f
  | _        => none

private def kDiv (x y : Float) : Float := x / y

private def kRecip (x : Float) : Float :=
  kDiv 1.0 x

private def div_vectors_core (v1 v2 : Array Float) : Array Float :=
  v1.zipWith (kDiv) v2

private def toFloatArray : KVal → Option (Array Float)
  | .vec v  => some (v.map Float.ofInt)
  | .fvec v => some v
  | _       => none

def kdiv (a b : KVal) : Except KError KVal :=
  match toFloat a, toFloat b with
  | some x, some y => .ok (.fatom (kDiv x y))
  | _, _ =>
    let va := toFloatArray a
    let vb := toFloatArray b
    match va, vb with
    | some v1, some v2 =>
      if v1.size = v2.size then
        .ok (.fvec (div_vectors_core v1 v2))
      else
        .error { kind := .length, message := s!"Cannot divide vector of length {v1.size} by vector of length {v2.size}" }
    | some v, none =>
      match toFloat b with
      | some y => .ok (.fvec (v.map (kDiv · y)))
      | none => .error { kind := .type, message := "'%' not supported between these types" }
    | none, some v =>
      match toFloat a with
      | some x => .ok (.fvec (v.map (kDiv x ·)))
      | none => .error { kind := .type, message := "'%' not supported between these types" }
    | none, none =>
      match a, b with
      | .box _, _ | _, .box _ => .error { kind := .type, message := "'%' not yet implemented for box values" }
      | .str _, _ | _, .str _ => .error { kind := .type, message := "'%' not supported on strings" }
      | .fn _, _ | _, .fn _ => .error { kind := .type, message := "'%' not supported on functions" }
      | _, _ => .error { kind := .type, message := "'%' not supported between these types" }

/-! ### Take / Reshape `#` -/

/-- Compute cyclic start position for negative take.
    For `n < 0`, we take from the tail, cycling if |n| > len. -/
private def negStart (len m : Nat) : Nat :=
  let r := m % len
  if r == 0 then 0 else len - r

/-- Cyclic fill: produce a list of length `m` by cycling through `src`
    starting at index `start`. `src` must be non-empty. -/
private def fillCyclicInt (src : Array Int) (start m : Nat) : Array Int :=
  let len := src.size
  (List.range m).toArray.map fun i => src[(start + i) % len]!

private def fillCyclicFloat (src : Array Float) (start m : Nat) : Array Float :=
  let len := src.size
  (List.range m).toArray.map fun i => src[(start + i) % len]!

private def fillCyclicChar (src : Array Char) (start m : Nat) : Array Char :=
  let len := src.size
  (List.range m).toArray.map fun i => src[(start + i) % len]!

private def fillCyclicKVal (src : Array KVal) (start m : Nat) : Array KVal :=
  let len := src.size
  (List.range m).toArray.map fun i =>
    let idx := (start + i) % len
    src.getD idx (.atom 0)

/-- Atom take: `n # y` where n is an integer. -/
private def takeAtom (n : Int) (y : KVal) : Except KError KVal :=
  let m := n.natAbs
  if m == 0 then
    match y with
    | .str _   => .ok (.str "")
    | .fvec _  => .ok (.fvec #[])
    | .fatom _ => .ok (.fvec #[])
    | _        => .ok (.vec #[])
  else
    match y with
    | .atom i =>
      .ok (.vec (Array.replicate m i))
    | .fatom f =>
      .ok (.fvec (Array.replicate m f))
    | .vec v =>
      if v.size == 0 then
        .error { kind := .domain, message := "'#' (take) cannot take from an empty list" }
      else
        let start := if n ≥ 0 then 0 else negStart v.size m
        .ok (.vec (fillCyclicInt v start m))
    | .fvec v =>
      if v.size == 0 then
        .error { kind := .domain, message := "'#' (take) cannot take from an empty list" }
      else
        let start := if n ≥ 0 then 0 else negStart v.size m
        .ok (.fvec (fillCyclicFloat v start m))
    | .str s =>
      if s.isEmpty then
        .error { kind := .domain, message := "'#' (take) cannot take from an empty string" }
      else
        let chars := s.toList.toArray
        let start := if n ≥ 0 then 0 else negStart chars.size m
        .ok (.str (String.ofList (fillCyclicChar chars start m).toList))
    | .box l =>
      if l.isEmpty then
        .error { kind := .domain, message := "'#' (take) cannot take from an empty list" }
      else
        let arr := l.toArray
        let start := if n ≥ 0 then 0 else negStart arr.size m
        .ok (fromList (fillCyclicKVal arr start m).toList)
    | .fn f =>
      .ok (.box (List.replicate m (.fn f)))

/-- Reshape: `dims # y` where dims is a vector of non-negative integers.
    Flattens y, fills cyclically to `product(dims)`, then nests into
    row-major shape. -/
private def reshape (dims : Array Int) (y : KVal) : Except KError KVal := do
  if dims.size == 0 then
    .error { kind := .domain, message := "'#' (reshape) requires at least one dimension" }
  else if dims.any (· < 0) then
    .error { kind := .domain, message := s!"'#' (reshape) dimensions must be non-negative, got {dims.toList}" }
  else
    let natDims := dims.map Int.toNat
    let total := natDims.foldl (· * ·) 1
    match y with
    | .str s =>
      if s.isEmpty && total > 0 then
        .error { kind := .domain, message := "'#' (reshape) cannot reshape an empty string" }
      else
        let chars := s.toList.toArray
        let flat := if total == 0 then #[] else fillCyclicChar chars 0 total
        .ok (reshapeChars natDims.toList flat 0)
    | _ =>
      let src := flattenToArray y
      if src.size == 0 && total > 0 then
        .error { kind := .domain, message := "'#' (reshape) cannot reshape an empty list" }
      else
        let flat := if total == 0 then #[] else fillCyclicKVal src 0 total
        .ok (reshapeKVals natDims.toList flat 0)
where
  flattenToArray (v : KVal) : Array KVal :=
    match v with
    | .atom i  => #[.atom i]
    | .fatom f => #[.fatom f]
    | .vec v   => v.map .atom
    | .fvec v  => v.map .fatom
    | .box l   => l.toArray
    | .str s   => #[.str s]
    | .fn f    => #[.fn f]
  reshapeKVals (dims : List Nat) (flat : Array KVal) (offset : Nat) : KVal :=
    match dims with
    | []      => .box []
    | [d]     => fromList (flat.toList.drop offset |>.take d)
    | d :: ds =>
      let chunkSize := ds.foldl (· * ·) 1
      let rows := List.range d |>.map fun i =>
        reshapeKVals ds flat (offset + i * chunkSize)
      .box rows
  reshapeChars (dims : List Nat) (flat : Array Char) (offset : Nat) : KVal :=
    match dims with
    | []      => .str ""
    | [d]     => .str (String.ofList (flat.toList.drop offset |>.take d))
    | d :: ds =>
      let chunkSize := ds.foldl (· * ·) 1
      let rows := List.range d |>.map fun i =>
        reshapeChars ds flat (offset + i * chunkSize)
      .box rows

def take_ (x y : KVal) : Except KError KVal :=
  match x with
  | .atom n   => takeAtom n y
  | .vec dims => reshape dims y
  | _         => .error { kind := .type,
                          message := s!"'#' (take/reshape) expects an integer or integer vector on the left, got {x}" }

def recip (x : KVal) : Except KError KVal :=
  match x with
  | .atom i  => .ok (.fatom (kRecip (Float.ofInt i)))
  | .fatom f => .ok (.fatom (kRecip f))
  | .vec v   => .ok (.fvec (v.map (fun i => kRecip (Float.ofInt i))))
  | .fvec v  => .ok (.fvec (v.map kRecip))
  | .box _   => .error { kind := .type, message := "'%' (reciprocal) not yet implemented for box values" }
  | .str _   => .error { kind := .type, message := "'%' (reciprocal) not supported on strings" }
  | .fn _    => .error { kind := .type, message := "'%' (reciprocal) not supported on functions" }
