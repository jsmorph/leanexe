import LeanExe.Extract.ScalarFunc

namespace BooleanLoopResultBindingTest

def rangeBoolResultLet (count seed : UInt64) : Bool :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  !flag

def rangeBoolResultDo (count seed : UInt64) : Id Bool := do
  let flag ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == seed % 7))
  pure (flag && seed != 0)

def rangeBoolResultFlag (count : UInt64) (flag : Bool) : Bool :=
  let selected :=
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if flag then 1 else 3)
      return a
    value != count
  selected != flag

def rangeBoolResultCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p (i.toUInt64 == 0) then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    value != seed
  p (!flag)

def rangeBoolResultSaved (count seed : UInt64) : Bool :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == 0
  let saved := !flag
  saved || seed == 0

def rangeBoolResultMixed (count seed : UInt64) : Bool :=
  let flag := if seed == 0 then count == 0 else
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == 0
  !flag && count != 0

def rangeBoolResultExit (count seed : UInt64) : Bool :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  flag || count == 0

def rangeBoolResultContinue (count seed : UInt64) : Id Bool := do
  let flag ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a)
    pure (value % 7 == seed % 7))
  pure (!flag || seed == 0)

def rangeBoolResultStride (count seed : UInt64) : Bool :=
  let flag :=
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:count.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  !flag

def rangeBoolResultId (count seed : UInt64) : Id (Id Bool) := do
  let flag : Id (Id Bool) ← (do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
      return a)
    pure (pure (pure (value % 7 == seed % 7))))
  pure (pure (!(Id.run (Id.run flag)) && seed != 0))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopResultBindingTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopResultBindingTest.rangeBoolResultLet, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultLet x y).toUInt64), true),
    (`BooleanLoopResultBindingTest.rangeBoolResultDo, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultDo x y).toUInt64), true),
    (`BooleanLoopResultBindingTest.rangeBoolResultFlag, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopResultBindingTest.rangeBoolResultCapture, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultCapture x y).toUInt64), true),
    (`BooleanLoopResultBindingTest.rangeBoolResultSaved, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultSaved x y).toUInt64), true),
    (`BooleanLoopResultBindingTest.rangeBoolResultMixed, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultMixed x y).toUInt64), true),
    (`BooleanLoopResultBindingTest.rangeBoolResultExit, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultExit x y).toUInt64), true),
    (`BooleanLoopResultBindingTest.rangeBoolResultContinue, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultContinue x y).toUInt64), true),
    (`BooleanLoopResultBindingTest.rangeBoolResultStride, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultStride x y).toUInt64), true),
    (`BooleanLoopResultBindingTest.rangeBoolResultId, (fun (x y : UInt64) => (BooleanLoopResultBindingTest.rangeBoolResultId x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop result-binding extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopResultBindingTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop result-binding IR comparisons passed"
