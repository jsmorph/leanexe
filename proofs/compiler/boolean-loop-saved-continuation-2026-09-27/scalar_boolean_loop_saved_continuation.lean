import LeanExe.Extract.ScalarFunc

namespace BooleanLoopSavedContinuationTest

def rangeBoolSavedCallWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  show Id Bool from do
    let argument ← (pure (count % 17) : Id (UInt64))
    run argument

def rangeBoolSavedCallFlag (count : UInt64) (flag : Bool) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := count
      for i in [:count.toNat] do
        a := a + i.toUInt64 + (if selected then 1 else 3)
      return a
    selected && value != count
  show Id Bool from do
    let argument ← (pure (!flag) : Id (Bool))
    run argument

def rangeBoolSavedCallBooleanArgument (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    selected || value % 5 == 0
  show Id Bool from do
    let argument ← (pure (seed % 2 == 0 && count != 0) : Id (Bool))
    run argument

def rangeBoolSavedCallWordCapture (count seed : UInt64) : Bool :=
  let f := fun x : UInt64 => x * 3 + seed
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := f seed
      for i in [:limit.toNat] do
        a := f a + i.toUInt64
      return a
    f value == f seed
  show Id Bool from do
    let argument ← (pure (count % 19) : Id (UInt64))
    run argument

def rangeBoolSavedCallBooleanCapture (count seed : UInt64) : Bool :=
  let p := fun flag : Bool => flag || seed == 0
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if p selected then a := a + i.toUInt64 + 1 else a := a + 3
      return a
    p selected && value != seed
  show Id Bool from do
    let argument ← (pure (p (count == 0)) : Id (Bool))
    run argument

def rangeBoolSavedCallNested (count seed : UInt64) : Bool :=
  let outer := fun selected : Bool =>
    let inner := fun limit : UInt64 =>
      let value := Id.run do
        let mut a := seed
        for i in [:limit.toNat] do
          a := a + i.toUInt64 + (if selected then 1 else 3)
        return a
      selected && value != seed
    show Id Bool from do
      let argument ← (pure (count % 17) : Id UInt64)
      inner argument
  show Id Bool from do
    let argument ← (pure (seed % 2 == 0) : Id (Bool))
    outer argument

def rangeBoolSavedCallExit (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    value % 7 == 0
  show Id Bool from do
    let argument ← (pure (count % 17) : Id (UInt64))
    run argument

def rangeBoolSavedCallContinue (count seed : UInt64) : Bool :=
  let run := fun selected : Bool =>
    let value := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if selected && i.toUInt64 % 2 == 0 then continue
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  show Id Bool from do
    let argument ← (pure (seed % 2 == 0) : Id (Bool))
    run argument

def rangeBoolSavedCallStride (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 5 == 0 then break
      return a
    value % 5 == 0
  show Id Bool from do
    let argument ← (pure (count % 23) : Id (UInt64))
    run argument

def rangeBoolSavedCallId (count seed : UInt64) : Id Bool :=
  let run (selected : Id (Id Bool)) : Id (Id Bool) := do
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if Id.run (Id.run selected) then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    pure (Id.run (Id.run selected) && value != seed)
  show Id Bool from do
    let argument ← (pure (pure (pure (seed % 2 == 0))) : Id (Id (Id Bool)))
    run argument

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopSavedContinuationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallWord, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallWord x y).toUInt64), true),
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallFlag, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallBooleanArgument, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallBooleanArgument x y).toUInt64), true),
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallWordCapture, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallWordCapture x y).toUInt64), true),
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallBooleanCapture, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallBooleanCapture x y).toUInt64), true),
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallNested, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallNested x y).toUInt64), true),
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallExit, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallExit x y).toUInt64), true),
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallContinue, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallContinue x y).toUInt64), true),
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallStride, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallStride x y).toUInt64), true),
    (`BooleanLoopSavedContinuationTest.rangeBoolSavedCallId, (fun (x y : UInt64) => (BooleanLoopSavedContinuationTest.rangeBoolSavedCallId x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop saved-continuation extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopSavedContinuationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop saved-continuation IR comparisons passed"
