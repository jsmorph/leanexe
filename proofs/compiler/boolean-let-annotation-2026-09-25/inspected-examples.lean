import LeanExe.Extract.ScalarFunc
namespace BooleanLetAnnotationInspect

def boolean (x y : UInt64) : UInt64 :=
  (let flag : Id Bool := x == 0; flag && y != 0).toUInt64 + x

def word (x y : UInt64) : UInt64 :=
  (let value : Id UInt64 := x + y; Id.run value == 0).toUInt64

def nested (x y : UInt64) : UInt64 :=
  (let flag : Id (Id Bool) := x == 0
   let value : Id (Id UInt64) := if flag && y != 0 then x + y else x - y
   let next : Id Bool := Id.run (Id.run value) != 0
   !(next : Bool)).toUInt64 + y

def helper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    (let saved : Id Bool := flag
     let value : Id UInt64 := if saved && outer then x + y else x - y
     (Id.run value == x) || (saved && !outer)).toUInt64
  f (y != 0)

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let word : Id UInt64 := a + UInt64.ofNat i
                    let stop : Id (Id Bool) := Id.run word % 7 == 0
                    (stop && seed != 0))
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag then break
  return a
end BooleanLetAnnotationInspect

run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanLetAnnotationInspect.boolean, `BooleanLetAnnotationInspect.word,
      `BooleanLetAnnotationInspect.nested, `BooleanLetAnnotationInspect.helper, `BooleanLetAnnotationInspect.range] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
