import LeanExe.Extract.ScalarFunc
namespace BooleanScopeApplicationProbe

def word (x y : UInt64) : UInt64 :=
  ((fun saved : UInt64 =>
    let f := fun n : UInt64 => n == saved
    f x || f y) (x + y)).toUInt64 + x

def flag (x y : UInt64) : UInt64 :=
  ((fun saved : Bool =>
    let f := fun b : Bool => b || saved
    f (x == 0) && f (y == 0)) (x == y)).toUInt64 + y

def nested (x y : UInt64) : UInt64 :=
  ((fun saved : UInt64 =>
    (fun flag : Bool =>
      let f := fun n : UInt64 => flag || n == saved
      f x && f y) (saved == y)) (x + y)).toUInt64 + x

def retained (x y : UInt64) : UInt64 :=
  ((fun saved : Id (Id UInt64) =>
    let f := fun n : UInt64 => n == Id.run (Id.run saved)
    f x || f y) (pure (pure (x + y)))).toUInt64 + y

def unused (x y : UInt64) : UInt64 :=
  ((fun _unused : Bool =>
    let f := fun n : UInt64 => n == y
    f x || f 0) (x == y)).toUInt64 + x

def choice (x y : UInt64) : UInt64 :=
  ((fun saved : UInt64 =>
    let f := fun n : UInt64 => n == saved
    f x || f y) (if x == 0 then y else x + y)).toUInt64 + y

end BooleanScopeApplicationProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanScopeApplicationProbe.word, `BooleanScopeApplicationProbe.flag,
      `BooleanScopeApplicationProbe.nested, `BooleanScopeApplicationProbe.retained,
      `BooleanScopeApplicationProbe.unused, `BooleanScopeApplicationProbe.choice] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
