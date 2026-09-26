import LeanExe.Extract.ScalarFunc
namespace BooleanDependentChoiceInspect
def equal (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let flag := if _h : a = b then b else !b
  flag.toUInt64 + x

def proposition (x y : UInt64) : UInt64 :=
  let flag := if _h : x < y then x == 0 else y != 0
  flag.toUInt64 + y

def nested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  let flag := if _h : a then
      if _k : a ≠ b then decide (a = b) else !b
    else if _j : x ≤ y then a == b else a != b
  flag.toUInt64

def capture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let value := if _h : flag = outer then
        (let g := fun z : UInt64 => z + x; g y) == x
      else !flag
    (if _k : value then outer else !outer).toUInt64 + x
  f (y != 0)

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    let flag ← pure (if _h : first ≠ second then !second else first)
    a := a + (if _k : flag then first else !second).toUInt64
    if flag then break
  return a
end BooleanDependentChoiceInspect
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanDependentChoiceInspect.equal, `BooleanDependentChoiceInspect.proposition,
      `BooleanDependentChoiceInspect.nested, `BooleanDependentChoiceInspect.capture, `BooleanDependentChoiceInspect.range] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
