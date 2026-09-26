import LeanExe.Extract.ScalarFunc
namespace IdArithmeticInspect

attribute [local reducible] Id

def left (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  a + y

def right (x y : UInt64) : UInt64 :=
  let b : Id (Id UInt64) := y
  x - b

def both (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  let b : Id (Id UInt64) := y
  a * b

def bitwise (x y : UInt64) : UInt64 :=
  let a : Id (Id UInt64) := x
  let b : Id UInt64 := y
  (a &&& b) ^^^ (a ||| b)

def range (count seed : UInt64) : UInt64 := Id.run do
  let bias : Id UInt64 := seed
  let mut a := seed
  for i in [:count.toNat] do
    let delta : Id (Id UInt64) := UInt64.ofNat i
    let current : Id UInt64 := a
    a := current + delta + bias
    if a % 7 == 0 && seed != 0 then break
  return a
end IdArithmeticInspect

set_option pp.all true in
run_elab do
  let env ← Lean.getEnv
  for name in [`IdArithmeticInspect.left, `IdArithmeticInspect.right, `IdArithmeticInspect.both,
      `IdArithmeticInspect.bitwise, `IdArithmeticInspect.range] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {value}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isSome}"
