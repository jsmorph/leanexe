import LeanExe.Extract.ScalarFunc

namespace BooleanLoopConditionalContinuationTest

def rangeBoolConditionalCallSaved (count seed : UInt64) : Id Bool :=
  do
    let flag ← if count == 0 then pure (seed == 0) else pure (seed % 2 == 0)
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if flag then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    return flag && value != seed

def rangeBoolConditionalCallNested (count seed : UInt64) : Id Bool :=
  do
    let flag ← if count == 0 then pure (seed == 0) else if seed % 3 == 0 then pure true else pure (seed % 2 == 0)
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if flag then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    return flag && value != seed

def rangeBoolConditionalCallExit (count seed : UInt64) : Id Bool :=
  do
    let flag ← if count < seed then pure (seed % 2 != 0) else pure (seed % 3 == 0)
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
        if flag && a % 7 == 0 then break
      return a)
    return flag || value == 0

def rangeBoolConditionalCallContinue (count seed : UInt64) : Bool :=
  Id.run do
    let flag ← if count == 0 then pure (seed % 3 == 0) else pure (seed % 2 == 0)
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if flag && i.toUInt64 % 3 == 0 then continue
        a := a + i.toUInt64 + 1
      return a)
    return flag && value == seed

def rangeBoolConditionalCallCapture (count seed : UInt64) : Id Bool :=
  do
    let flag ← if count < seed then pure (seed % 7 == 0) else pure (seed == 0)
    let value ← (do
      let f := fun b : Bool => if b && flag then seed + 7 else seed + 3
      let mut a := f false
      for i in [:count.toNat] do
        a := a + f (i.toUInt64 % 2 == 0)
      return a)
    return flag || value == seed

def rangeBoolConditionalCallHelper (count seed : UInt64) : Id Bool :=
  let p := fun x : UInt64 => x % 3 == seed % 3
  do
    let flag ← if p count then pure (p seed) else pure (p (count + 1))
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if flag then a := a + i.toUInt64 + 1 else a := a + 3
      return a)
    return flag && value != seed

def rangeBoolConditionalCallFlag (count : UInt64) (input : Bool) : Id Bool :=
  do
    let flag ← if input then pure (count % 2 == 0) else pure (!input)
    let value ← (do
      let mut a := input.toUInt64
      for i in [:count.toNat] do
        a := a + i.toUInt64 + flag.toUInt64
      return a)
    return flag && value != input.toUInt64

def rangeBoolConditionalCallStride (count seed : UInt64) : Id Bool :=
  do
    let limit ← if seed % 2 == 0 then pure (count % 17) else pure (count % 11)
    let value ← (do
      let mut a := seed
      for i in [(seed % 3).toNat:limit.toNat:3] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a)
    return value % 7 == 0

def rangeBoolConditionalCallWord (count seed : UInt64) : Bool :=
  let run := fun limit : UInt64 =>
    let value := Id.run do
      let mut a := seed
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
      return a
    value % 7 == seed % 7
  if seed % 2 == 0 then run (count % 17) else run (count % 11)

def rangeBoolConditionalCallId (count seed : UInt64) : Id (Id Bool) :=
  do
    let flag : Id Bool ← if count < seed then pure (pure (seed % 2 == 0)) else pure (pure (seed % 3 == 0))
    let value ← (do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + i.toUInt64 + 1
        if Id.run flag && a % 7 == 0 then break
      return a)
    return pure (Id.run flag && value != seed)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopConditionalContinuationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallSaved, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallSaved x y).toUInt64), true),
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallNested, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallNested x y).toUInt64), true),
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallExit, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallExit x y).toUInt64), true),
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallContinue, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallContinue x y).toUInt64), true),
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallCapture, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallCapture x y).toUInt64), true),
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallHelper, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallHelper x y).toUInt64), true),
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallFlag, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallFlag x (y != 0)).toUInt64), true),
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallStride, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallStride x y).toUInt64), true),
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallWord, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallWord x y).toUInt64), true),
    (`BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallId, (fun (x y : UInt64) => (BooleanLoopConditionalContinuationTest.rangeBoolConditionalCallId x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop conditional-continuation extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopConditionalContinuationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop conditional-continuation IR comparisons passed"
