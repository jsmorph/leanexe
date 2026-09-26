import LeanExe.Extract.ScalarFunc
namespace BooleanPropositionInspect
def equal (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  if a = b then x + y else x - y
def unequal (x y : UInt64) : UInt64 :=
  let a := x == y
  let b := decide (x < y)
  if a ≠ b then x + 7 else y - 11
def literals (x y : UInt64) : UInt64 :=
  let flag := x != 0
  if flag = false then x + y else if true ≠ flag then x - y else y
def dependent (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun flag : Bool =>
    if _h : flag = outer then
      let g := fun other : Bool => if other ≠ flag then x + y else x - y
      g (y == 0)
    else (flag != outer).toUInt64 + x
  f (y != 0)
def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    if first = second then a := a + 3 else a := a + 7
    if _h : first ≠ second then break
  return a
end BooleanPropositionInspect
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanPropositionInspect.equal, `BooleanPropositionInspect.unequal,
      `BooleanPropositionInspect.literals, `BooleanPropositionInspect.dependent, `BooleanPropositionInspect.range] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
