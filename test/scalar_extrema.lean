import LeanExe.Extract.ScalarFunc

namespace ExtremaTest

def minimumOrder (x y : UInt64) : UInt64 := min x y

def maximumOrder (x y : UInt64) : UInt64 := max x y

def extremaNested (x y : UInt64) : UInt64 := max (min x y) (min (~~~x) (~~~y))

def extremaClamped (x y : UInt64) : UInt64 :=
  let lo := min x y
  let hi := max x y
  min hi (max lo (x + y))

def extremaFunction (x y : UInt64) : UInt64 :=
  let captured := max x 7
  let f := fun a b : UInt64 => min (max a captured) (b + 17)
  f x y + max (f y x) (min x y)

def extremaDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := min x y
  let z ← if x < y then pure (max a (x + y)) else pure (min a (x * y))
  a := max (a + 3) z
  return min a (x ^^^ y)

def extremaGuard (x y : UInt64) : UInt64 :=
  if (min x y == 0 || max x y == x) ∧ min (x + y) (~~~y) ≤ max x y
  then max (x / y) (y % x) else min (~~~x) (~~~y)

def extremaWrapped (x y : UInt64) : UInt64 :=
  min (x + 1) (y - 1) + max (x * 3) (y <<< x) - min (x >>> y) (~~~y)

def rangeExtremaCount (count seed : UInt64) : UInt64 := Id.run do
  let mut a := min seed 17
  for i in [:(max (count % 17) (seed % 7)).toNat] do
    a := max (a + 1) (UInt64.ofNat i + seed)
  return min a (seed + 31)

def rangeExtremaExit (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if min (UInt64.ofNat i % 3) (seed % 3) == 1 then continue
    a := min (max a (a + UInt64.ofNat i)) (seed + 17)
    if max a (UInt64.ofNat i) % 5 == seed % 5 then break
  return max a seed

def rangeExtremaBounds (count seed : UInt64) : UInt64 :=
  let first := min seed 18446744073709551613
  let result := Id.run do
    let mut a := seed
    for i in [first.toNat:(first + min count 2).toNat] do
      a := max (min a (UInt64.ofNat i)) (a + 1)
    return a
  min (max result seed) (result + count)

def rangeExtremaStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if min x y = seed ∨ (max x y == 0 && UInt64.ofNat i % 3 == 0)
      then .done (max x y) else .yield (min (x + UInt64.ofNat i) (y + 3))
    finish (a + 1) (a + seed)

def minimumCustom (x y : UInt64) : UInt64 :=
  @Min.min UInt64 ⟨fun a b => a + b⟩ x y

def maximumCustom (x y : UInt64) : UInt64 :=
  @Max.max UInt64 ⟨fun a b => a * b⟩ x y

def extremaUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => @Min.min UInt64 ⟨fun a b => a ^^^ b⟩ z y
  max x y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end ExtremaTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`ExtremaTest.minimumOrder, ExtremaTest.minimumOrder, false),
    (`ExtremaTest.maximumOrder, ExtremaTest.maximumOrder, false),
    (`ExtremaTest.extremaNested, ExtremaTest.extremaNested, false),
    (`ExtremaTest.extremaClamped, ExtremaTest.extremaClamped, false),
    (`ExtremaTest.extremaFunction, ExtremaTest.extremaFunction, false),
    (`ExtremaTest.extremaDo, ExtremaTest.extremaDo, false),
    (`ExtremaTest.extremaGuard, ExtremaTest.extremaGuard, false),
    (`ExtremaTest.extremaWrapped, ExtremaTest.extremaWrapped, false),
    (`ExtremaTest.rangeExtremaCount, ExtremaTest.rangeExtremaCount, true),
    (`ExtremaTest.rangeExtremaExit, ExtremaTest.rangeExtremaExit, true),
    (`ExtremaTest.rangeExtremaBounds, ExtremaTest.rangeExtremaBounds, true),
    (`ExtremaTest.rangeExtremaStep, ExtremaTest.rangeExtremaStep, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: min/max extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else ExtremaTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`ExtremaTest.minimumCustom, `ExtremaTest.maximumCustom, `ExtremaTest.extremaUnusedCustom] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported min/max instance accepted"
  Lean.logInfo "208 native/min-max IR comparisons and three rejection tests passed"
