import LeanExe.Extract.ScalarFunc

namespace ScalarLoopSequenceTest

def rangeSequenceDirect (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  for i in [:count.toNat] do a := a * 3 + i.toUInt64
  return a

def rangeSequenceDependent (count seed : UInt64) : Id UInt64 := do
  let mut a := seed % 7
  for i in [:count.toNat] do a := (a + i.toUInt64) % 7
  let mut b := seed
  for i in [:a.toNat] do b := b + a + i.toUInt64
  return a + b

def rangeSequenceExits (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64
    if a % 7 == 0 then break
  let mut b := a
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    b := b + i.toUInt64
    if b % 11 == 0 then break
  return a + b

def rangeSequenceUnused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := seed
  for i in [:count.toNat] do b := b + i.toUInt64 * 3
  return b

def rangeSequenceThree (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  for i in [:count.toNat] do a := a * 3 + i.toUInt64
  for i in [:count.toNat] do a := a ^^^ i.toUInt64
  return a

def rangeSequenceShadow (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let seed := seed + 7
  let mut b := seed
  for i in [:count.toNat] do b := b + a + i.toUInt64
  return a + b + seed

def rangeSequenceIdBind (count seed : UInt64) : Id UInt64 := do
  let first : Id (Id UInt64) := do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64
    return a
  let a ← first
  let b ← (do
    let mut b : UInt64 := a
    for i in [:count.toNat] do b := b * 3 + i.toUInt64
    return b : Id UInt64)
  return UInt64.add a b

def rangeSequenceBoolInput (count : UInt64) (flag : Bool) : Id UInt64 := do
  let mut a := flag.toUInt64
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := a
  for i in [:count.toNat] do b := if flag then b + i.toUInt64 else b + 3
  return a + b

end ScalarLoopSequenceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`ScalarLoopSequenceTest.rangeSequenceDirect, (fun (x y : UInt64) => ScalarLoopSequenceTest.rangeSequenceDirect x y)),
    (`ScalarLoopSequenceTest.rangeSequenceDependent, (fun (x y : UInt64) => ScalarLoopSequenceTest.rangeSequenceDependent x y)),
    (`ScalarLoopSequenceTest.rangeSequenceExits, (fun (x y : UInt64) => ScalarLoopSequenceTest.rangeSequenceExits x y)),
    (`ScalarLoopSequenceTest.rangeSequenceUnused, (fun (x y : UInt64) => ScalarLoopSequenceTest.rangeSequenceUnused x y)),
    (`ScalarLoopSequenceTest.rangeSequenceThree, (fun (x y : UInt64) => ScalarLoopSequenceTest.rangeSequenceThree x y)),
    (`ScalarLoopSequenceTest.rangeSequenceShadow, (fun (x y : UInt64) => ScalarLoopSequenceTest.rangeSequenceShadow x y)),
    (`ScalarLoopSequenceTest.rangeSequenceIdBind, (fun (x y : UInt64) => ScalarLoopSequenceTest.rangeSequenceIdBind x y)),
    (`ScalarLoopSequenceTest.rangeSequenceBoolInput, (fun (x y : UInt64) => ScalarLoopSequenceTest.rangeSequenceBoolInput x (y != 0)))]
  let inputs := ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
    ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: sequence extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for (x, y) in inputs do
      let actual := module_.evalFunc 0 [x, y]
      let expected := native x y
      unless actual == expected do throwError "{name}({x}, {y}): {actual} != {expected}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected count {comparisons}"
  Lean.logInfo m!"{comparisons} native/sequential-loop IR comparisons passed"
