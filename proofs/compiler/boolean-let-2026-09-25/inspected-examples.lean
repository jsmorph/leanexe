import LeanExe.Extract.ScalarFunc
namespace BooleanLetInspect

def nested (x y : UInt64) : UInt64 :=
  (let flag := x == 0; flag && y != 0).toUInt64 + x

def capture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let flag := (let localFlag := y == 0; ((if localFlag then x else y) == x) || outer)
  flag.toUInt64 + y

def shadow (x y : UInt64) : UInt64 :=
  let a := x != 0
  (let a := a; let a := !a; a != false).toUInt64 + y

def unused (x y : UInt64) : UInt64 :=
  (let _unused := x == y; y != 0).toUInt64

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let even := a % 2 == 0; (if even then a else UInt64.ofNat i) != seed)
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag then break
  return a
end BooleanLetInspect

run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanLetInspect.nested, `BooleanLetInspect.capture, `BooleanLetInspect.shadow,
      `BooleanLetInspect.unused, `BooleanLetInspect.range] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
