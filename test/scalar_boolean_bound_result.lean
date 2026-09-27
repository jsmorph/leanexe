import LeanExe.Extract.ScalarFunc

namespace BooleanBoundResultTest

def booleanBoundResultValue (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let saved := f (x == 0); saved).toUInt64 + y

def booleanBoundResultBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  (let saved := x != 0; f (!saved)).toUInt64 + x

def booleanBoundResultNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let saved := f (x == 0); let saved := f (!saved); f saved).toUInt64 + y

def booleanBoundResultCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => let saved := f b; f (!saved)
  (g (x == 0)).toUInt64 + (g true).toUInt64

def booleanBoundResultApplication (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  ((fun saved : Bool => f (!saved)) (f (x == 0))).toUInt64 + x

def booleanBoundResultNamed (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let transform := fun saved : Bool => f (!saved); transform (f (x == 0))).toUInt64 + y

def rangeBooleanBoundResultStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    a := a + (let saved := f (i.toUInt64 == seed); f (!saved)).toUInt64 + 1
  return a

def rangeBooleanBoundResultCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (let saved := f (i.toUInt64 == seed); f (!saved)) then break
    a := a + i.toUInt64 + 1
  return a

def rangeBooleanBoundResultOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved := (let flag := f true; f (!flag))
  let mut a := seed + saved.toUInt64
  for i in [:count.toNat] do
    if (let flag := f (a == i.toUInt64); f (!flag)) then
      a := a + 3
      continue
    a := a + 1
  return a + saved.toUInt64

def rangeBooleanBoundResultHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => let saved := f b; f (!saved)
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => let saved := g b; f (!saved)
    if h (a == i.toUInt64) then break
    a := a + (g true).toUInt64 + 1
  return a + (g false).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanBoundResultTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanBoundResultTest.booleanBoundResultValue, BooleanBoundResultTest.booleanBoundResultValue, false),
    (`BooleanBoundResultTest.booleanBoundResultBody, BooleanBoundResultTest.booleanBoundResultBody, false),
    (`BooleanBoundResultTest.booleanBoundResultNested, BooleanBoundResultTest.booleanBoundResultNested, false),
    (`BooleanBoundResultTest.booleanBoundResultCapture, BooleanBoundResultTest.booleanBoundResultCapture, false),
    (`BooleanBoundResultTest.booleanBoundResultApplication, BooleanBoundResultTest.booleanBoundResultApplication, false),
    (`BooleanBoundResultTest.booleanBoundResultNamed, BooleanBoundResultTest.booleanBoundResultNamed, false),
    (`BooleanBoundResultTest.rangeBooleanBoundResultStep, BooleanBoundResultTest.rangeBooleanBoundResultStep, true),
    (`BooleanBoundResultTest.rangeBooleanBoundResultCondition, BooleanBoundResultTest.rangeBooleanBoundResultCondition, true),
    (`BooleanBoundResultTest.rangeBooleanBoundResultOuter, BooleanBoundResultTest.rangeBooleanBoundResultOuter, true),
    (`BooleanBoundResultTest.rangeBooleanBoundResultHelper, BooleanBoundResultTest.rangeBooleanBoundResultHelper, true)]
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
      else BooleanBoundResultTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean bound-result IR comparisons passed"
