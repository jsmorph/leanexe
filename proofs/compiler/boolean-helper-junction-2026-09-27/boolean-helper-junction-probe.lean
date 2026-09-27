import LeanExe.Extract.ScalarFunc
open LeanExe.Extract.Core
namespace BooleanHelperJunctionProbe

def left (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) && (x == 0)).toUInt64 + x

def right (x y : UInt64) : UInt64 :=
  ((x == 0) || (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0))).toUInt64 + x

def both (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) &&
    !(let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))).toUInt64 + x

def dependent (x y : UInt64) : UInt64 :=
  if _h : ((let f := fun n : UInt64 => n == y; f x || f 0) ||
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))) then x + 7 else y + 11

def exit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if ((let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) &&
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))) then break
  return a
end BooleanHelperJunctionProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanHelperJunctionProbe.left, `BooleanHelperJunctionProbe.right,
      `BooleanHelperJunctionProbe.both, `BooleanHelperJunctionProbe.dependent, `BooleanHelperJunctionProbe.exit] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(extractScalarFunc name none info.type value).isSome}"
