import LeanExe.Extract.ScalarFunc

namespace BooleanWordBoundResultTest

def booleanWordBoundResultValue (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let saved := x + (f true).toUInt64; f (saved == y)).toUInt64 + y

def booleanWordBoundResultBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  (let saved := x + y; f (saved == 0)).toUInt64 + x

def booleanWordBoundResultNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let saved := x + 1; let saved := saved + y; f (saved == y)).toUInt64 + y

def booleanWordBoundResultCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun n : UInt64 => let saved := n + x; f (saved == y)
  (g y).toUInt64 + (g x).toUInt64

def booleanWordBoundResultApplication (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  ((fun saved : UInt64 => f (saved == y)) (x + (f true).toUInt64)).toUInt64 + x

def booleanWordBoundResultNamed (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (let transform := fun saved : UInt64 => f (saved == y); transform (x + (f true).toUInt64)).toUInt64 + y

def rangeBooleanWordBoundResultStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    a := a + (let saved := a + i.toUInt64; f (saved == seed)).toUInt64 + 1
  return a

def rangeBooleanWordBoundResultCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (let saved := a + i.toUInt64; f (saved != seed)) then break
    a := a + i.toUInt64 + 1
  return a

def rangeBooleanWordBoundResultOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved := (let value := seed + 1; f (value == 0))
  let mut a := seed + saved.toUInt64
  for i in [:count.toNat] do
    if (let value := a + i.toUInt64; f (value == seed)) then
      a := a + 3
      continue
    a := a + 1
  return a + saved.toUInt64

def rangeBooleanWordBoundResultHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => let saved := n + seed; f (saved == 0)
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun n : UInt64 => let saved := n + a; g saved
    if h i.toUInt64 then break
    a := a + (g a).toUInt64 + 1
  return a + (g seed).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanWordBoundResultTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanWordBoundResultTest.booleanWordBoundResultValue, BooleanWordBoundResultTest.booleanWordBoundResultValue, false),
    (`BooleanWordBoundResultTest.booleanWordBoundResultBody, BooleanWordBoundResultTest.booleanWordBoundResultBody, false),
    (`BooleanWordBoundResultTest.booleanWordBoundResultNested, BooleanWordBoundResultTest.booleanWordBoundResultNested, false),
    (`BooleanWordBoundResultTest.booleanWordBoundResultCapture, BooleanWordBoundResultTest.booleanWordBoundResultCapture, false),
    (`BooleanWordBoundResultTest.booleanWordBoundResultApplication, BooleanWordBoundResultTest.booleanWordBoundResultApplication, false),
    (`BooleanWordBoundResultTest.booleanWordBoundResultNamed, BooleanWordBoundResultTest.booleanWordBoundResultNamed, false),
    (`BooleanWordBoundResultTest.rangeBooleanWordBoundResultStep, BooleanWordBoundResultTest.rangeBooleanWordBoundResultStep, true),
    (`BooleanWordBoundResultTest.rangeBooleanWordBoundResultCondition, BooleanWordBoundResultTest.rangeBooleanWordBoundResultCondition, true),
    (`BooleanWordBoundResultTest.rangeBooleanWordBoundResultOuter, BooleanWordBoundResultTest.rangeBooleanWordBoundResultOuter, true),
    (`BooleanWordBoundResultTest.rangeBooleanWordBoundResultHelper, BooleanWordBoundResultTest.rangeBooleanWordBoundResultHelper, true)]
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
      else BooleanWordBoundResultTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean word-bound-result IR comparisons passed"
