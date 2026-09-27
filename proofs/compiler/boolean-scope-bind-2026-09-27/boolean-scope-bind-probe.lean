import LeanExe.Extract.ScalarFunc
namespace BooleanScopeBindProbe

def word (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (x + y) : Id UInt64)
    let f := fun n : Id UInt64 => (Id.run n) == saved
    return f x || f y).toUInt64 + x

def flag (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (x == y) : Id Bool)
    let f := fun b : Id Bool => Id.run b || saved
    return f (x == 0) && f (y == 0)).toUInt64 + y

def nested (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (x + y) : Id UInt64)
    let flag ← (pure (saved == y) : Id Bool)
    let f := fun n : UInt64 => flag || n == saved
    return f x && f y).toUInt64 + x

def retained (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (pure (x + y)) : Id (Id UInt64))
    let f := fun n : UInt64 => n == Id.run saved
    return f x || f y).toUInt64 + y

def unused (x y : UInt64) : UInt64 :=
  (Id.run do
    let _unused ← (pure (x == y) : Id Bool)
    let f := fun n : UInt64 => n == y
    return f x || f 0).toUInt64 + x

def choice (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (if x == 0 then pure y else pure (x + y) : Id UInt64)
    let f := fun n : UInt64 => n == saved
    return f x || f y).toUInt64 + y

end BooleanScopeBindProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanScopeBindProbe.word, `BooleanScopeBindProbe.flag,
      `BooleanScopeBindProbe.nested, `BooleanScopeBindProbe.retained,
      `BooleanScopeBindProbe.unused, `BooleanScopeBindProbe.choice] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
