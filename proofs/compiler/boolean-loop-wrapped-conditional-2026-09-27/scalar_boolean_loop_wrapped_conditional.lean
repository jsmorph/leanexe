import LeanExe.Extract.ScalarFunc

namespace BooleanLoopWrappedConditionalTest

def rangeBoolWrappedChoiceWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  Id.run (if count % 2 == 0 then run (count % 17) else run (count % 7))

def rangeBoolWrappedChoiceFlag (count : UInt64) (flag : Bool) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if selected then 1 else 3)
      return a
    selected && value != count
  show Id Bool from if count % 2 == 0 then run (!flag) else run (count % 3 == 0)

def rangeBoolWrappedChoiceBooleanArgument (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    selected || value % 5 == 0
  Id.run (pure (if count % 2 == 0 then run (seed % 2 == 0 && count != 0) else run (count % 3 == 0)) : Id Bool)

def rangeBoolWrappedChoiceWordCapture (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x * 3 + seed
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := f seed
      for i in [:limit.toNat] do
        a := f a + i.toUInt64
      return a
    f value == f seed
  Id.run (if count % 2 == 0 then run (count % 19) else run (count % 7))

def rangeBoolWrappedChoiceBooleanCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    p selected && value != seed
  show Id Bool from if count % 2 == 0 then run (p (count == 0)) else run (count % 3 == 0)

def rangeBoolWrappedChoiceNested (count seed : UInt64) : Bool :=
  let outer := fun selected : Bool =>
    let inner := fun limit : UInt64 =>
      let value := Id.run do
        let mut a := seed
        for i in [:limit.toNat] do
          a := a + i.toUInt64 + (if selected then 1 else 3)
        return a
      selected && value != seed
    inner (count % 17)
  Id.run (pure (if count % 2 == 0 then outer (seed % 2 == 0) else outer (count % 3 == 0)) : Id Bool)

def rangeBoolWrappedChoiceExit (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  Id.run (if count % 2 == 0 then run (count % 17) else run (count % 7))

def rangeBoolWrappedChoiceContinue (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected && i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  show Id Bool from if count % 2 == 0 then run (seed % 2 == 0) else run (count % 3 == 0)

def rangeBoolWrappedChoiceStride (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  Id.run (pure (if count % 2 == 0 then run (count % 23) else run (count % 7)) : Id Bool)

def rangeBoolWrappedChoiceId (count seed : UInt64) : Id Bool :=
  let run (selected : Id (Id Bool)) : Id (Id Bool) := do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if Id.run (Id.run selected) then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    pure (Id.run (Id.run selected) && value != seed)
  Id.run (if count % 2 == 0 then run (pure (pure (seed % 2 == 0))) else run (pure (pure false)))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopWrappedConditionalTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceWord, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceWord x y).toUInt64), true),
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceFlag, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceBooleanArgument, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceBooleanArgument x y).toUInt64), true),
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceWordCapture, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceWordCapture x y).toUInt64), true),
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceBooleanCapture, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceBooleanCapture x y).toUInt64), true),
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceNested, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceNested x y).toUInt64), true),
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceExit, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceExit x y).toUInt64), true),
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceContinue, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceContinue x y).toUInt64), true),
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceStride, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceStride x y).toUInt64), true),
    (`BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceId, (fun (x y : UInt64) => (BooleanLoopWrappedConditionalTest.rangeBoolWrappedChoiceId x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop wrapped-conditional extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopWrappedConditionalTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop wrapped-conditional IR comparisons passed"
