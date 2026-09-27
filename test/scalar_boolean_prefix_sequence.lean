import LeanExe.Extract.ScalarEnvironmentFunc

namespace BooleanPrefixSequenceTest

def rangeBooleanPrefixWord (count seed : UInt64) : Id UInt64 := do
  let mut flag := false
  for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
  let mut a := seed
  for i in [:count.toNat] do a := if flag then a + i.toUInt64 else a * 3
  return a

def rangeBooleanPrefixBoolean (count seed : UInt64) : Id Bool := do
  let mut flag := false
  for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
  let mut result := flag
  for i in [:count.toNat] do result := result != (i.toUInt64 % 3 == 0)
  return result

def rangeBooleanPrefixDependent (count seed : UInt64) : Id UInt64 := do
  let mut flag := seed == 0
  for i in [:count.toNat] do flag := flag != (i.toUInt64 == seed)
  let bound := if flag then count else count % 7
  let mut a := seed + flag.toUInt64
  for i in [:bound.toNat] do a := a + i.toUInt64
  return a

def rangeBooleanPrefixExits (count seed : UInt64) : Id Bool := do
  let mut flag := false
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    flag := flag || i.toUInt64 == seed % 7
    if flag then break
  let mut result := flag
  for i in [:count.toNat] do
    result := result != (i.toUInt64 % 5 == 0)
    if result then break
  return result

def rangeBooleanPrefixUnused (count seed : UInt64) : Id UInt64 := do
  let mut flag := false
  for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  return a

def rangeBooleanPrefixAlternating (count seed : UInt64) : Id Bool := do
  let mut flag := false
  for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
  let mut a := seed + flag.toUInt64
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut result := flag
  for i in [:count.toNat] do result := result || i.toUInt64 == a % 7
  return result


def rangeBooleanPrefixRetained (count seed : UInt64) : Id UInt64 := do
  let first : Id (Id Bool) := do
    let mut flag := false
    for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
    return flag
  let flag ← first
  let mut a := seed + flag.toUInt64
  for i in [:count.toNat] do a := if Bool.and flag true then a + i.toUInt64 else a * 3
  return a

def rangeBooleanPrefixCapture (count seed : UInt64) : Id UInt64 := do
  let mut flag := false
  for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
  let captured := flag
  let f := fun x : UInt64 => if captured then x + seed else x * 3
  let captured := seed == 0
  let mut a := seed
  for i in [:count.toNat] do a := f (a + i.toUInt64)
  return a + captured.toUInt64

end BooleanPrefixSequenceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanPrefixSequenceTest.rangeBooleanPrefixWord, (fun (x y : UInt64) => BooleanPrefixSequenceTest.rangeBooleanPrefixWord x y)),
    (`BooleanPrefixSequenceTest.rangeBooleanPrefixBoolean, (fun (x y : UInt64) => (BooleanPrefixSequenceTest.rangeBooleanPrefixBoolean x y).toUInt64)),
    (`BooleanPrefixSequenceTest.rangeBooleanPrefixDependent, (fun (x y : UInt64) => BooleanPrefixSequenceTest.rangeBooleanPrefixDependent x y)),
    (`BooleanPrefixSequenceTest.rangeBooleanPrefixExits, (fun (x y : UInt64) => (BooleanPrefixSequenceTest.rangeBooleanPrefixExits x y).toUInt64)),
    (`BooleanPrefixSequenceTest.rangeBooleanPrefixUnused, (fun (x y : UInt64) => BooleanPrefixSequenceTest.rangeBooleanPrefixUnused x y)),
    (`BooleanPrefixSequenceTest.rangeBooleanPrefixAlternating, (fun (x y : UInt64) => (BooleanPrefixSequenceTest.rangeBooleanPrefixAlternating x y).toUInt64)),
    (`BooleanPrefixSequenceTest.rangeBooleanPrefixRetained, (fun (x y : UInt64) => BooleanPrefixSequenceTest.rangeBooleanPrefixRetained x y)),
    (`BooleanPrefixSequenceTest.rangeBooleanPrefixCapture, (fun (x y : UInt64) => BooleanPrefixSequenceTest.rangeBooleanPrefixCapture x y))]
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
  Lean.logInfo m!"{comparisons} native/Boolean-prefix sequential-loop IR comparisons passed"
