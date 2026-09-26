import LeanExe.Extract.ScalarFunc

namespace ReusableBooleanTest

def reusableBooleanTwice (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n == y
  if f x || f (x + 1) then x + 7 else y - 3

def reusableBooleanCapture (x y : UInt64) : UInt64 :=
  let flag := x != 0
  let shift := fun n : UInt64 => n + y
  let f := fun n : UInt64 => flag && shift n != x
  (f x).toUInt64 + (f y).toUInt64 * 3

def reusableBooleanNested (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n == y
  let g := fun n : UInt64 => !f n && f (n + 1)
  if g x then (f y).toUInt64 + x else (g y).toUInt64 + y

def reusableBooleanScalarCapture (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n != y
  let g := fun n : UInt64 => if f n then n + 1 else n * 3
  g x + g y

def reusableBooleanShadow (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n == x
  let saved := f y
  let f := fun n : UInt64 => saved || n != y
  if f x && f y then x - y else x + y

def reusableBooleanDependent (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => if _h : n < y then n != x else n == y
  if _h : f x then (f y).toUInt64 + x else (f (x + 1)).toUInt64 + y

def reusableBooleanId (x y : UInt64) : UInt64 :=
  let f : UInt64 → Id (Id Bool) := fun n => n == y
  (f x).toUInt64 + (f (x + 1)).toUInt64

def reusableBooleanUnused (x y : UInt64) : UInt64 :=
  let _f := fun n : UInt64 => n / y == x
  x - y

def reusableBooleanIgnoredArgument (x y : UInt64) : UInt64 :=
  let f := fun _n : UInt64 => x == y
  (f (x / y)).toUInt64 + (f (y / x)).toUInt64

def reusableBooleanDo (x y : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n != y
  let a ← pure (f x)
  let b ← pure (f (x + 1))
  if a && b then return x + y else return x - y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end ReusableBooleanTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`ReusableBooleanTest.reusableBooleanTwice, ReusableBooleanTest.reusableBooleanTwice),
    (`ReusableBooleanTest.reusableBooleanCapture, ReusableBooleanTest.reusableBooleanCapture),
    (`ReusableBooleanTest.reusableBooleanNested, ReusableBooleanTest.reusableBooleanNested),
    (`ReusableBooleanTest.reusableBooleanScalarCapture, ReusableBooleanTest.reusableBooleanScalarCapture),
    (`ReusableBooleanTest.reusableBooleanShadow, ReusableBooleanTest.reusableBooleanShadow),
    (`ReusableBooleanTest.reusableBooleanDependent, ReusableBooleanTest.reusableBooleanDependent),
    (`ReusableBooleanTest.reusableBooleanId, ReusableBooleanTest.reusableBooleanId),
    (`ReusableBooleanTest.reusableBooleanUnused, ReusableBooleanTest.reusableBooleanUnused),
    (`ReusableBooleanTest.reusableBooleanIgnoredArgument, ReusableBooleanTest.reusableBooleanIgnoredArgument),
    (`ReusableBooleanTest.reusableBooleanDo, ReusableBooleanTest.reusableBooleanDo)]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reusable Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for (x, y) in ReusableBooleanTest.inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 140 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/reusable-Boolean IR comparisons passed"
