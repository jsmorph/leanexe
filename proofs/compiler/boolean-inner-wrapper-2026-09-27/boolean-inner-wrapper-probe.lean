import LeanExe.Extract.ScalarFunc
open LeanExe.Extract.Core
namespace BooleanInnerWrapperProbe

def direct (x y : UInt64) : UInt64 :=
  (Id.run do
    let f := fun n : UInt64 => n == y
    return f x || f 0).toUInt64 + x

def condition (x y : UInt64) : UInt64 :=
  if (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0)) then x + 7 else y + 11

def pureValue (x y : UInt64) : UInt64 :=
  (pure (let f := fun n : UInt64 => n == y; f x || f 0) : Id Bool).toUInt64 + x

def nested (x y : UInt64) : UInt64 :=
  (Id.run (pure (let f := fun n : UInt64 => n == y; f x || f 0) : Id (Id Bool))).toUInt64 + x

def exit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (Id.run do
      let f := fun n : UInt64 => n % 7 == 0
      return f a || f (i.toUInt64 + 1)) then break
  return a
end BooleanInnerWrapperProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanInnerWrapperProbe.direct, `BooleanInnerWrapperProbe.condition,
      `BooleanInnerWrapperProbe.pureValue, `BooleanInnerWrapperProbe.nested, `BooleanInnerWrapperProbe.exit] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(extractScalarFunc name none info.type value).isSome}"
