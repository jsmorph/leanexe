import LeanExe.Extract.ScalarFunc
namespace BooleanLetAnnotationInspect

def boolean (x y : UInt64) : UInt64 :=
  (let flag : Id Bool := x == 0; flag && y != 0).toUInt64 + x

def word (x y : UInt64) : UInt64 :=
  (let value : Id UInt64 := x + y; value == 0).toUInt64

def nested (x y : UInt64) : UInt64 :=
  (let flag : Id (Id Bool) := x == 0
   let value : Id (Id UInt64) := if flag then x + y else x - y
   let next : Id Bool := value != 0
   !next).toUInt64 + y

def helper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    (let saved : Id Bool := flag
     let value : Id UInt64 := if saved then x + y else x - y
     if _h : saved = outer then value == x else value != y).toUInt64
  f (y != 0)

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let word : Id UInt64 := a + UInt64.ofNat i
                    let stop : Id (Id Bool) := word % 7 == 0
                    stop)
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
