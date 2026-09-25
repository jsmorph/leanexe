import LeanExe.Extract.ScalarFunc
namespace BooleanEqualityInspect
def direct (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  (a == b).toUInt64 + (a != b).toUInt64 * 3
def calls (x y : UInt64) : UInt64 :=
  let a := x == y
  let b := decide (x < y)
  (BEq.beq a b).toUInt64 + (bne a b).toUInt64
def conditional (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y != 0
  if a == b then x + y else x - y
def capture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun flag : Bool => if flag != outer then x + y else x - y
  f (y == 0)
def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    a := a + (first == second).toUInt64
    if first != second then break
  return a
end BooleanEqualityInspect
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanEqualityInspect.direct, `BooleanEqualityInspect.calls,
      `BooleanEqualityInspect.conditional, `BooleanEqualityInspect.capture, `BooleanEqualityInspect.range] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
