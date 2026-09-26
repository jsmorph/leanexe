import LeanExe.Extract.ScalarFunc
namespace BooleanWordInspect
def direct (x y : UInt64) : UInt64 := (x == y).toUInt64 + Bool.toUInt64 (decide (x < y))
def captured (x y : UInt64) : UInt64 :=
  let flag := x != 0
  let f := fun flag : Bool => flag.toUInt64 + x
  f (!flag) + flag.toUInt64 * y
def action (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x = y then pure true else pure (decide (x > 0))
  return flag.toUInt64 + x

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (decide (UInt64.ofNat i % 2 = 0)).toUInt64
    if a % 7 == 0 then break
  return a
end BooleanWordInspect
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanWordInspect.direct, `BooleanWordInspect.captured,
      `BooleanWordInspect.action, `BooleanWordInspect.range] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
