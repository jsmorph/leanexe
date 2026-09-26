import LeanExe.Extract.ScalarFunc
namespace BooleanWordLetInspect

def original (x y : UInt64) : UInt64 :=
  (let word := x + y; word == 0).toUInt64

def mixed (x y : UInt64) : UInt64 :=
  let outer := x == 0
  (let word := if outer then x + y else x - y
   let flag := word == 0
   let more := word + y
   flag || more == x).toUInt64 + y

def shadow (x y : UInt64) : UInt64 :=
  (let x := x + y; let x := x * 3; x != y).toUInt64 + x

def helper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  (let word := (let f := fun flag : Bool => if flag then x + y else x - y; f outer)
   if _h : word ≤ x then word == y else word != x).toUInt64

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let word := a + UInt64.ofNat i; word % 7 == 0)
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag then break
  return a
end BooleanWordLetInspect

run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanWordLetInspect.original, `BooleanWordLetInspect.mixed, `BooleanWordLetInspect.shadow,
      `BooleanWordLetInspect.helper, `BooleanWordLetInspect.range] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
