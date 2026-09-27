import LeanExe.Extract.ScalarFunc

namespace BooleanLoopWrappedContinuationTest

def rangeBoolWrappedCallWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  Id.run (run (count % 17))

def rangeBoolWrappedCallFlag (count : UInt64) (flag : Bool) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if selected then 1 else 3)
      return a
    selected && value != count
  Id.run (pure (run (!flag)) : Id Bool)

def rangeBoolWrappedCallBooleanArgument (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    selected || value % 5 == 0
  Id.run (Id.run (pure (pure (run (seed % 2 == 0 && count != 0))) : Id (Id Bool)))

def rangeBoolWrappedCallWordCapture (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x * 3 + seed
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := f seed
      for i in [:limit.toNat] do
        a := f a + i.toUInt64
      return a
    f value == f seed
  Id.run (run (count % 19))

def rangeBoolWrappedCallBooleanCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    p selected && value != seed
  Id.run (pure (run (p (count == 0))) : Id Bool)

def rangeBoolWrappedCallNested (count seed : UInt64) : Bool :=
  let outer := fun selected : Bool =>
    let inner := fun limit : UInt64 =>
      let value := Id.run do
        let mut a := seed
        for i in [:limit.toNat] do
          a := a + i.toUInt64 + (if selected then 1 else 3)
        return a
      selected && value != seed
    Id.run (inner (count % 17))
  Id.run (Id.run (pure (pure (outer (seed % 2 == 0))) : Id (Id Bool)))

def rangeBoolWrappedCallExit (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  Id.run (run (count % 17))

def rangeBoolWrappedCallContinue (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected && i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  Id.run (pure (run (seed % 2 == 0)) : Id Bool)

def rangeBoolWrappedCallStride (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  Id.run (Id.run (pure (pure (run (count % 23))) : Id (Id Bool)))

def rangeBoolWrappedCallId (count seed : UInt64) : Id Bool :=
  let run (selected : Id (Id Bool)) : Id (Id Bool) := do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if Id.run (Id.run selected) then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    pure (Id.run (Id.run selected) && value != seed)
  Id.run (run (pure (pure (seed % 2 == 0))))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopWrappedContinuationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallWord, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallWord x y).toUInt64), true),
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallFlag, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallBooleanArgument, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallBooleanArgument x y).toUInt64), true),
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallWordCapture, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallWordCapture x y).toUInt64), true),
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallBooleanCapture, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallBooleanCapture x y).toUInt64), true),
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallNested, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallNested x y).toUInt64), true),
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallExit, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallExit x y).toUInt64), true),
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallContinue, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallContinue x y).toUInt64), true),
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallStride, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallStride x y).toUInt64), true),
    (`BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallId, (fun (x y : UInt64) => (BooleanLoopWrappedContinuationTest.rangeBoolWrappedCallId x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop wrapped-continuation extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopWrappedContinuationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop wrapped-continuation IR comparisons passed"
