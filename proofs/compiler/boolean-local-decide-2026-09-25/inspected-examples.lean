import LeanExe.Extract.ScalarFunc
namespace BooleanLocalDecideInspect
def equal (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  (decide (a = b)).toUInt64 + (decide (a ≠ b)).toUInt64 * 3
def truth (x y : UInt64) : UInt64 :=
  let flag := x != y
  (decide flag).toUInt64 + (decide (flag = true)).toUInt64 * 7

def implicit (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y == 0
  let same : Bool := a = b
  let different : Bool := a ≠ b
  (same && different).toUInt64 + (same || different).toUInt64

def nested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let first := decide ((decide (a = b)) ≠ (decide (a = false)))
  if _h : !first then x + y else x - y

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := a % 2 == 0
    let other := UInt64.ofNat i % 3 == 0
    let same ← pure (decide (even = other))
    a := a + same.toUInt64
    if !even ≠ other then break
  return a
end BooleanLocalDecideInspect
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanLocalDecideInspect.equal, `BooleanLocalDecideInspect.truth,
      `BooleanLocalDecideInspect.implicit, `BooleanLocalDecideInspect.nested, `BooleanLocalDecideInspect.range] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
