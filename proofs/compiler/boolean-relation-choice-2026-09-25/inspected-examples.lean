import LeanExe.Extract.ScalarFunc
namespace BooleanRelationChoiceInspect
def equal (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let flag := if a = b then a else !b
  flag.toUInt64 + x

def unequal (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y != 0
  (if a ≠ b then a == b else decide (a = b)).toUInt64 + y

def nested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let left := if a = false then !b else if b ≠ true then a else !a
  let right := if (if a then b else !b) = (if x < y then a else !a) then left else !left
  (if left ≠ right then !a else b).toUInt64

def capture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let value := if flag = outer then decide (flag ≠ false) else !flag
    let g := fun other : Bool => (if other ≠ flag then value else !value).toUInt64 + x
    g (y == 0)
  f (y != 0)

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    let same ← if first = second then pure first else pure (!second)
    a := a + (if same ≠ first then same else second).toUInt64
    if same then break
  return a
end BooleanRelationChoiceInspect
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanRelationChoiceInspect.equal, `BooleanRelationChoiceInspect.unequal,
      `BooleanRelationChoiceInspect.nested, `BooleanRelationChoiceInspect.capture, `BooleanRelationChoiceInspect.range] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
