import LeanExe.Extract.ScalarFunc
open LeanExe.Extract.Core
namespace BooleanHelperCompositeProbe

def negated (x y : UInt64) : UInt64 :=
  (!(let f := fun n : UInt64 => n == y; f x || f 0)).toUInt64 + x

def junction (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) && (x == 0)).toUInt64 + x

def equality (x y : UInt64) : UInt64 :=
  ((let f := fun n : UInt64 => n == y; f x || f 0) == (x == 0)).toUInt64 + x

def choice (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) then x == 0 else y == 0).toUInt64 + x

def helperBody (x y : UInt64) : UInt64 :=
  (let f := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0)
   f x && f y).toUInt64 + x

def identityInput (x y : UInt64) : UInt64 :=
  (let f := fun n : Id UInt64 => Id.run n == y; f x || f 0).toUInt64 + x
end BooleanHelperCompositeProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanHelperCompositeProbe.negated, `BooleanHelperCompositeProbe.junction,
      `BooleanHelperCompositeProbe.equality, `BooleanHelperCompositeProbe.choice,
      `BooleanHelperCompositeProbe.helperBody, `BooleanHelperCompositeProbe.identityInput] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(extractScalarFunc name none info.type value).isSome}"
