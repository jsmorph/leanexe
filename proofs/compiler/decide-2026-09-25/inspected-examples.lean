import LeanExe.Extract.ScalarFunc
namespace DecideInspect
def explicit (x y : UInt64) : UInt64 :=
  let flag := decide (x < y)
  if flag then x + y else x - y
def implicit (x y : UInt64) : UInt64 :=
  let flag : Bool := x ≤ y
  if flag then x + y else x - y
def compound (x y : UInt64) : UInt64 :=
  let flag := decide ((x < y ∧ y ≠ 0) ∨ ¬ (x = y))
  if !flag then x + y else x - y
def boolean (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => if flag then x + y else x - y
  f (decide ((x == y) = true))
def rangeBoolFnBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let flag ← if a % 7 = 0 then pure true else pure (UInt64.ofNat i ≥ 12)
    if flag then break
  return a
end DecideInspect
run_elab do
  let env ← Lean.getEnv
  for name in [`DecideInspect.explicit, `DecideInspect.implicit, `DecideInspect.compound,
      `DecideInspect.boolean, `DecideInspect.rangeBoolFnBreak] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
