import LeanExe.Extract.ScalarFunc

namespace WordLoopConditionalTest

def rangeWordChooseLoops (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then Id.run do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64 + 1
    return a
  else Id.run do
    let mut a := seed + 7
    for i in [:count.toNat] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseScalarLeft (count seed : UInt64) : UInt64 :=
  if seed < count then seed * 7 + count else Id.run do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64 + 1
    return a

def rangeWordChooseScalarRight (count seed : UInt64) : UInt64 :=
  if seed % 3 == 0 then Id.run do
    let mut a := seed + 7
    for i in [:count.toNat] do a := a * 3 + i.toUInt64
    return a
  else seed * 7 + count

def rangeWordChooseNested (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then
    if count % 3 == 0 then Id.run do
      let mut a := seed
      for i in [:count.toNat] do a := a + i.toUInt64 + 1
      return a
    else seed + count * 3
  else
    if seed < count then seed * 7 else Id.run do
      let mut a := seed + 7
      for i in [:count.toNat] do a := a * 3 + i.toUInt64
      return a

def rangeWordChooseBooleanLoop (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then
    let flag :=
      let value := Id.run do
        let mut a := seed
        for i in [:count.toNat] do a := a + i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then seed + count else seed * 3
  else Id.run do
    let mut a := seed + 7
    for i in [:count.toNat] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseExit (count seed : UInt64) : UInt64 :=
  if seed % 3 == 0 then Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a
  else Id.run do
    let mut a := seed + 7
    for i in [:count.toNat] do
      a := a * 3 + i.toUInt64
      if a % 11 == 0 then break
    return a

def rangeWordChooseContinue (count seed : UInt64) : Id UInt64 := do
  if seed % 2 == 0 then
    let mut a := seed
    for i in [:count.toNat] do
      if i.toUInt64 % 2 == 0 then continue
      a := a + i.toUInt64 + 1
    return a
  else
    let mut a := seed + 7
    for i in [:count.toNat] do
      if i.toUInt64 % 3 == 0 then continue
      a := a * 3 + i.toUInt64
    return a

def rangeWordChooseStride (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then Id.run do
    let mut a := seed
    for i in [1:count.toNat:3] do a := a + i.toUInt64 + 1
    return a
  else Id.run do
    let mut a := seed + 7
    for i in [2:count.toNat:5] do a := a * 3 + i.toUInt64
    return a

def rangeWordChooseHelpers (count seed : UInt64) : UInt64 :=
  if seed % 2 == 0 then
    let bump : UInt64 → UInt64 := fun x => x + seed % 7
    let flag :=
      let value := Id.run do
        let mut a := bump seed
        for i in [:count.toNat] do a := a + bump i.toUInt64 + 1
        return a
      value % 7 == seed % 7
    if flag then bump count else bump seed * 3
  else
    let combine : UInt64 → UInt64 → UInt64 := fun x y => x * 3 + y + seed
    Id.run do
      let mut a := combine seed 1
      for i in [:count.toNat] do a := combine a i.toUInt64
      return a

def rangeWordChooseId (count seed : UInt64) : Id (Id UInt64) :=
  Id.run (pure (if seed % 2 == 0 then (Id.run do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64 + 1
    return a) else seed * 7 + count) : Id (Id UInt64))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end WordLoopConditionalTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`WordLoopConditionalTest.rangeWordChooseLoops, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseLoops x y), true),
    (`WordLoopConditionalTest.rangeWordChooseScalarLeft, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseScalarLeft x y), true),
    (`WordLoopConditionalTest.rangeWordChooseScalarRight, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseScalarRight x y), true),
    (`WordLoopConditionalTest.rangeWordChooseNested, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseNested x y), true),
    (`WordLoopConditionalTest.rangeWordChooseBooleanLoop, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseBooleanLoop x y), true),
    (`WordLoopConditionalTest.rangeWordChooseExit, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseExit x y), true),
    (`WordLoopConditionalTest.rangeWordChooseContinue, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseContinue x y), true),
    (`WordLoopConditionalTest.rangeWordChooseStride, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseStride x y), true),
    (`WordLoopConditionalTest.rangeWordChooseHelpers, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseHelpers x y), true),
    (`WordLoopConditionalTest.rangeWordChooseId, (fun (x y : UInt64) => WordLoopConditionalTest.rangeWordChooseId x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: word-loop conditional extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else WordLoopConditionalTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/word-loop conditional IR comparisons passed"
