import LeanExe.Extract.ScalarEnvironmentFunc

namespace BooleanLoopSequenceTest

def rangeBooleanSequenceDirect (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b

def rangeBooleanSequenceDependent (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := a == seed
  for i in [:(a % 7).toNat] do b := b != (i.toUInt64 == seed)
  return b

def rangeBooleanSequenceExits (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64
    if a % 7 == 0 then break
  let mut b := false
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    b := b || i.toUInt64 == a % 11
    if b then break
  return b

def rangeBooleanSequenceUnused (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == seed
  return b

def rangeBooleanSequenceThree (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  for i in [:count.toNat] do a := a * 3 + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b

def rangeBooleanSequenceRetained (count seed : UInt64) : Id (Id Bool) := do
  let first : Id (Id UInt64) := do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64
    return a
  let a ← first
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b


def rangeBooleanSequenceBoolInput (count : UInt64) (flag : Bool) : Id Bool := do
  let mut a := flag.toUInt64
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := flag
  for i in [:count.toNat] do b := b != (i.toUInt64 == a % 7)
  return b

def rangeBooleanSequenceWordTail (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := a
  for i in [:count.toNat] do b := b * 3 + i.toUInt64
  return b % 7 == a % 7

end BooleanLoopSequenceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanLoopSequenceTest.rangeBooleanSequenceDirect, (fun (x y : UInt64) => (BooleanLoopSequenceTest.rangeBooleanSequenceDirect x y).toUInt64)),
    (`BooleanLoopSequenceTest.rangeBooleanSequenceDependent, (fun (x y : UInt64) => (BooleanLoopSequenceTest.rangeBooleanSequenceDependent x y).toUInt64)),
    (`BooleanLoopSequenceTest.rangeBooleanSequenceExits, (fun (x y : UInt64) => (BooleanLoopSequenceTest.rangeBooleanSequenceExits x y).toUInt64)),
    (`BooleanLoopSequenceTest.rangeBooleanSequenceUnused, (fun (x y : UInt64) => (BooleanLoopSequenceTest.rangeBooleanSequenceUnused x y).toUInt64)),
    (`BooleanLoopSequenceTest.rangeBooleanSequenceThree, (fun (x y : UInt64) => (BooleanLoopSequenceTest.rangeBooleanSequenceThree x y).toUInt64)),
    (`BooleanLoopSequenceTest.rangeBooleanSequenceRetained, (fun (x y : UInt64) => (BooleanLoopSequenceTest.rangeBooleanSequenceRetained x y).toUInt64)),
    (`BooleanLoopSequenceTest.rangeBooleanSequenceBoolInput, (fun (x y : UInt64) => (BooleanLoopSequenceTest.rangeBooleanSequenceBoolInput x (y != 0)).toUInt64)),
    (`BooleanLoopSequenceTest.rangeBooleanSequenceWordTail, (fun (x y : UInt64) => (BooleanLoopSequenceTest.rangeBooleanSequenceWordTail x y).toUInt64))]
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
  Lean.logInfo m!"{comparisons} native/Boolean-result sequential-loop IR comparisons passed"
