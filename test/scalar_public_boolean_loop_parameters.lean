import LeanExe.Extract.ScalarFunc

namespace PublicBooleanLoopParametersTest

def rangeFlagYield (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let mut a := flag.toUInt64
  for i in [:count.toNat] do
    a := a + i.toUInt64 + flag.toUInt64
  return a

def rangeFlagExit (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let mut a : UInt64 := 1
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if flag && a % 7 == 0 then break
  return a

def rangeFlagContinue (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let mut a := count
  for i in [:count.toNat] do
    if flag && i.toUInt64 % 3 == 0 then continue
    a := a + i.toUInt64 + 1
  return a

def rangeFlagsBoth (left right : Bool) : UInt64 := Id.run do
  let n : UInt64 := if left then 7 else 3
  let mut a := right.toUInt64
  for i in [:n.toNat] do
    a := a + i.toUInt64 + left.toUInt64
    if right && a % 5 == 0 then break
  return a

def rangeFlagOuter (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let f := fun b : Bool => if b then count + flag.toUInt64 else count - flag.toUInt64
  let mut a := f false
  for i in [:count.toNat] do
    a := a + f (i.toUInt64 % 2 == 0)
  return a

def rangeFlagStepHelper (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let mut a := count
  for i in [:count.toNat] do
    let f := fun b : Bool => if b then a + flag.toUInt64 else a + i.toUInt64
    a := f flag
    if a % 11 == 0 then break
  return a

def rangeFlagAlias (count : UInt64) (flag : Bool) : UInt64 := Id.run do
  let saved := !flag
  let mut a := count + saved.toUInt64
  for i in [:count.toNat] do
    if saved then a := a + i.toUInt64 else a := a + 1
  return a

def rangeFlagBind (count : UInt64) (flag : Bool) : Id UInt64 := do
  let saved ← pure flag
  let mut a := count
  for i in [:count.toNat] do
    if !saved && i.toUInt64 % 2 == 0 then continue
    a := a + i.toUInt64 + saved.toUInt64
  return a

def rangeFlagCount (flag : Bool) (count : UInt64) : UInt64 := Id.run do
  let stop := count % 17 + flag.toUInt64
  let mut a : UInt64 := if flag then 1 else 7
  for i in [:stop.toNat] do
    a := a + i.toUInt64
  return a

def rangeFlagResult (flag : Bool) (count : UInt64) : UInt64 := Id.run do
  let stop := count % 17
  let mut a := count
  for i in [:stop.toNat] do
    a := a + i.toUInt64
    if flag && a % 7 == 0 then break
  return if flag then a + count else a - count

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PublicBooleanLoopParametersTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PublicBooleanLoopParametersTest.rangeFlagYield, (fun x y => PublicBooleanLoopParametersTest.rangeFlagYield x (y != 0)), true),
    (`PublicBooleanLoopParametersTest.rangeFlagExit, (fun x y => PublicBooleanLoopParametersTest.rangeFlagExit x (y != 0)), true),
    (`PublicBooleanLoopParametersTest.rangeFlagContinue, (fun x y => PublicBooleanLoopParametersTest.rangeFlagContinue x (y != 0)), true),
    (`PublicBooleanLoopParametersTest.rangeFlagsBoth, (fun x y => PublicBooleanLoopParametersTest.rangeFlagsBoth (x != 0) (y != 0)), true),
    (`PublicBooleanLoopParametersTest.rangeFlagOuter, (fun x y => PublicBooleanLoopParametersTest.rangeFlagOuter x (y != 0)), true),
    (`PublicBooleanLoopParametersTest.rangeFlagStepHelper, (fun x y => PublicBooleanLoopParametersTest.rangeFlagStepHelper x (y != 0)), true),
    (`PublicBooleanLoopParametersTest.rangeFlagAlias, (fun x y => PublicBooleanLoopParametersTest.rangeFlagAlias x (y != 0)), true),
    (`PublicBooleanLoopParametersTest.rangeFlagBind, (fun x y => Id.run (PublicBooleanLoopParametersTest.rangeFlagBind x (y != 0))), true),
    (`PublicBooleanLoopParametersTest.rangeFlagCount, (fun x y => PublicBooleanLoopParametersTest.rangeFlagCount (x != 0) y), true),
    (`PublicBooleanLoopParametersTest.rangeFlagResult, (fun x y => PublicBooleanLoopParametersTest.rangeFlagResult (x != 0) y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: public parameter extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PublicBooleanLoopParametersTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/public Boolean loop parameter IR comparisons passed"
