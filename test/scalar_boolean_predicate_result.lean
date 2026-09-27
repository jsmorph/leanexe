import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateResultTest

def booleanPredicateResultBool (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b && x != 0
  let g := fun b : Bool => f b
  (g (x == y)).toUInt64 + (g true).toUInt64

def booleanPredicateResultWord (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || y == 0
  let g := fun n : UInt64 => f (n == x)
  if g y then x + 7 else y + (g x).toUInt64

def booleanPredicateResultNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  let g := fun b : Bool => f b && f (x == y)
  let h := fun n : UInt64 => if n < y then g (f false) else f (g (n == x))
  (h x).toUInt64 + (g (h y)).toUInt64 * 3

def booleanPredicateResultCapture (x y : UInt64) : UInt64 :=
  let saved := x == 0
  let f := fun b : Bool => b || saved
  let g := fun b : Bool => f b && y != 0
  let f := fun b : Bool => !b
  let g := fun b : Bool => g (f b)
  if _h : g (x == y) then x + 3 else y + (g false).toUInt64

def booleanPredicateResultUnused (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x / y == 0
  let _unused := fun _n : UInt64 => f true
  let g := fun b : Bool => f true || f b
  x + y + (g false).toUInt64

def booleanPredicateResultWrapped (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == y
  let g : Bool → Id (Id Bool) := fun b => pure (Id.run (pure (f b)))
  let h : Id (Id UInt64) → Id Bool := fun n => pure (g ((show UInt64 from n) == y))
  (h x).toUInt64 + (g false).toUInt64

def rangeBooleanPredicateResultStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let delta := Id.run do
      let f := fun b : Bool => b || a == 0
      let g := fun b : Bool => f b
      return if g (UInt64.ofNat i % 3 == 0) then 3 else 1
    a := a + UInt64.ofNat i + delta
    if a % 7 == 0 then break
  return a

def rangeBooleanPredicateResultCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (Id.run do
      let f := fun b : Bool => !b || a == seed
      let g := fun n : UInt64 => f (n % 3 == 0)
      return (g (UInt64.ofNat i)).toUInt64) == 0 then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateResultOuter (count seed : UInt64) : UInt64 := Id.run do
  let extra := Id.run do
    let f := fun b : Bool => b || seed == 0
    let g := fun b : Bool => f b
    return (g (count == 0)).toUInt64
  let mut a := seed + extra
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if a % 7 == 0 then break
  return a

def rangeBooleanPredicateResultHelper (count seed : UInt64) : UInt64 := Id.run do
  let h := fun value : UInt64 =>
    let f := fun b : Bool => !b && seed != 0
    let g := fun b : Bool => f b
    if g (value == seed) then value + 3 else value - 1
  let mut a := seed
  for i in [:count.toNat] do
    a := h a + UInt64.ofNat i
    if a % 11 == 0 then break
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateResultTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateResultTest.booleanPredicateResultBool, BooleanPredicateResultTest.booleanPredicateResultBool, false),
    (`BooleanPredicateResultTest.booleanPredicateResultWord, BooleanPredicateResultTest.booleanPredicateResultWord, false),
    (`BooleanPredicateResultTest.booleanPredicateResultNested, BooleanPredicateResultTest.booleanPredicateResultNested, false),
    (`BooleanPredicateResultTest.booleanPredicateResultCapture, BooleanPredicateResultTest.booleanPredicateResultCapture, false),
    (`BooleanPredicateResultTest.booleanPredicateResultUnused, BooleanPredicateResultTest.booleanPredicateResultUnused, false),
    (`BooleanPredicateResultTest.booleanPredicateResultWrapped, BooleanPredicateResultTest.booleanPredicateResultWrapped, false),
    (`BooleanPredicateResultTest.rangeBooleanPredicateResultStep, BooleanPredicateResultTest.rangeBooleanPredicateResultStep, true),
    (`BooleanPredicateResultTest.rangeBooleanPredicateResultCondition, BooleanPredicateResultTest.rangeBooleanPredicateResultCondition, true),
    (`BooleanPredicateResultTest.rangeBooleanPredicateResultOuter, BooleanPredicateResultTest.rangeBooleanPredicateResultOuter, true),
    (`BooleanPredicateResultTest.rangeBooleanPredicateResultHelper, BooleanPredicateResultTest.rangeBooleanPredicateResultHelper, true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reusable Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanPredicateResultTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate helper result IR comparisons passed"
