import LeanExe.Extract.ScalarFunc
namespace BooleanHelperGeneralBodyProbe

def nested (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 =>
    let g := fun k : UInt64 => k == y
    g n || g 0
   f x && f y).toUInt64 + x

def wrapped (x y : UInt64) : UInt64 :=
  (let f := fun b : Bool => Id.run do
    let g := fun k : Bool => k || x == y
    return g b && g (y == 0)
   f (x == 0) || f (x == y)).toUInt64 + y

def unused (x y : UInt64) : UInt64 :=
  (let _unused := fun n : UInt64 =>
    let g := fun k : UInt64 => k == y
    g n || g 0
   x == y).toUInt64 + x

def propLet (x y : UInt64) : UInt64 :=
  if x < y ∧ (let f := fun n : UInt64 =>
      let g := fun k : UInt64 => k == y
      g n || g 0
    f x && f y) then x + 7 else y + 3

def identityInput (x y : UInt64) : UInt64 :=
  (let f := fun n : Id UInt64 => (Id.run n) == y
   f x && f 0).toUInt64 + x

end BooleanHelperGeneralBodyProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanHelperGeneralBodyProbe.nested, `BooleanHelperGeneralBodyProbe.wrapped,
      `BooleanHelperGeneralBodyProbe.unused, `BooleanHelperGeneralBodyProbe.propLet,
      `BooleanHelperGeneralBodyProbe.identityInput] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
