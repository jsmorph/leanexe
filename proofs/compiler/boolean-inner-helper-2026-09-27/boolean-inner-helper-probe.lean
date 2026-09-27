import LeanExe.Extract.ScalarFunc
open LeanExe.Extract.Core
namespace BooleanInnerHelperProbe

def word (x y : UInt64) : UInt64 :=
  let flag := (let f := fun n : UInt64 => n == y; f x || f y)
  flag.toUInt64 + x

def boolean (x y : UInt64) : UInt64 :=
  let flag := (let f := fun b : Bool => b && y != 0; f (x == y) || f (x == 0))
  flag.toUInt64 + x

def condition (x y : UInt64) : UInt64 :=
  if (let f := fun n : UInt64 => n == y; f x || f y) then x + 7 else y + 3

def wrapped (x y : UInt64) : UInt64 :=
  (Id.run do
    let f := fun n : UInt64 => n == y
    return f x || f y).toUInt64 + x

def wordHelper (x y : UInt64) : UInt64 :=
  let flag := (let f := fun n : UInt64 => n + y; f x == f y)
  flag.toUInt64 + x
end BooleanInnerHelperProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanInnerHelperProbe.word, `BooleanInnerHelperProbe.boolean,
      `BooleanInnerHelperProbe.condition, `BooleanInnerHelperProbe.wrapped, `BooleanInnerHelperProbe.wordHelper] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(extractScalarFunc name none info.type value).isSome}"
