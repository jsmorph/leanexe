import LeanExe.Extract.ScalarFunc

namespace WordLoopBindingTest

def rangeWordChooseSetupWord (count seed : UInt64) : UInt64 :=
  let limit := count % 17
  let initial := seed + 7
  if initial % 3 == 0 then Id.run do
    let mut a := initial
    for i in [:limit.toNat] do a := a + i.toUInt64 + 1
    return a
  else initial * 3 + limit

def rangeWordChooseSetupFlag (count seed : UInt64) : UInt64 :=
  let selected := seed % 3 == 0
  let initial := if selected then seed + 7 else seed * 3
  if selected then Id.run do
    let mut a := initial
    for i in [:count.toNat] do a := a + i.toUInt64 + 1
    return a
  else Id.run do
    let mut a := initial + 11
    for i in [:count.toNat] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseSetupDo (count seed : UInt64) : Id UInt64 := do
  let limit ← pure (count % 17)
  let initial ← pure (seed + 7)
  if initial % 3 == 0 then
    let mut a := initial
    for i in [:limit.toNat] do a := a + i.toUInt64 + 1
    return a
  else pure (initial * 3 + limit)

def rangeWordChooseSetupNested (count seed : UInt64) : Id UInt64 := do
  let selected ← pure (seed % 3 == 0)
  let limit := count % 17
  let initial ← pure (if selected then seed + 7 else seed * 3)
  if selected then
    let mut a := initial
    for i in [:limit.toNat] do a := a + i.toUInt64 + 1
    return a
  else if limit < 7 then pure (initial + 11) else
    let mut a := initial + 11
    for i in [:limit.toNat] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseSavedResult (count seed : UInt64) : UInt64 :=
  let saved :=
    if seed % 2 == 0 then Id.run do
      let mut a := seed
      for i in [:count.toNat] do a := a + i.toUInt64 + 1
      return a
    else seed * 3 + count
  let again := saved + seed * 3
  again * 7 + saved

def rangeWordChooseShowResult (count seed : UInt64) : Id UInt64 :=
  show Id UInt64 from do
    let saved ← (if seed % 2 == 0 then (do
      let mut a := seed
      for i in [:count.toNat] do a := a + i.toUInt64 + 1
      return a) else pure (seed * 3 + count))
    pure (saved * 7 + seed)

def rangeWordChooseSetupExit (count seed : UInt64) : UInt64 :=
  let limit := count % 23
  let initial := seed + 11
  let saved := if initial % 3 == 0 then Id.run do
      let mut a := initial
      for i in [:limit.toNat] do
        a := a + i.toUInt64 + 1
        if a % 7 == 0 then break
      return a
    else initial * 7
  if saved % 5 == 0 then saved + limit else saved * 3

def rangeWordChooseSetupContinue (count seed : UInt64) : Id UInt64 := do
  let selected ← pure (seed % 2 == 0)
  let initial := if selected then seed + 5 else seed * 3
  let saved ← (if selected then (do
    let mut a := initial
    for i in [:count.toNat] do
      if i.toUInt64 % 2 == 0 then continue
      a := a + i.toUInt64 + 1
    return a) else pure (initial + 11))
  pure (saved + count)

def rangeWordChooseSetupStride (count seed : UInt64) : UInt64 :=
  let initial := seed + 11
  let saved := if initial % 2 == 0 then Id.run do
      let mut a := initial
      for i in [1:count.toNat:3] do a := a + i.toUInt64 + 1
      return a
    else Id.run do
      let mut a := initial + 7
      for i in [2:count.toNat:5] do a := a * 3 + i.toUInt64
      return a
  saved + initial

def rangeWordChooseSetupId (count seed : UInt64) : Id (Id UInt64) := do
  let limit : Id (Id UInt64) ← pure (count % 17)
  let selected : Id (Id Bool) ← pure (seed % 2 == 0)
  let stop := Id.run (Id.run limit)
  let flag := Id.run (Id.run selected)
  let saved : Id (Id UInt64) ← (if flag then (do
    let mut a := seed
    for i in [:stop.toNat] do a := a + i.toUInt64 + 1
    return a) else pure (seed * 3))
  pure (Id.run (Id.run saved) + stop)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end WordLoopBindingTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`WordLoopBindingTest.rangeWordChooseSetupWord, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseSetupWord x y), true),
    (`WordLoopBindingTest.rangeWordChooseSetupFlag, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseSetupFlag x y), true),
    (`WordLoopBindingTest.rangeWordChooseSetupDo, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseSetupDo x y), true),
    (`WordLoopBindingTest.rangeWordChooseSetupNested, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseSetupNested x y), true),
    (`WordLoopBindingTest.rangeWordChooseSavedResult, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseSavedResult x y), true),
    (`WordLoopBindingTest.rangeWordChooseShowResult, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseShowResult x y), true),
    (`WordLoopBindingTest.rangeWordChooseSetupExit, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseSetupExit x y), true),
    (`WordLoopBindingTest.rangeWordChooseSetupContinue, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseSetupContinue x y), true),
    (`WordLoopBindingTest.rangeWordChooseSetupStride, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseSetupStride x y), true),
    (`WordLoopBindingTest.rangeWordChooseSetupId, (fun (x y : UInt64) => WordLoopBindingTest.rangeWordChooseSetupId x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: word-loop binding extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else WordLoopBindingTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/word-loop binding IR comparisons passed"
