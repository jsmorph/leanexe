import LeanExe.Extract.ScalarFunc
namespace ActionChoiceInspect
def ordinary (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x < y then pure (x == 0) else pure (y != 0)
  return if flag then x + y else x - y
def boolean (x y : UInt64) : UInt64 := Id.run do
  let saved := x == y
  let flag ← if saved then pure (!saved) else pure (x != 0)
  return if flag then x + y else x - y
def nested (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x == y then Id.run (pure (x != 0)) else
    if x < y then pure (y == 0) else pure (x == 0)
  return if flag then x + y else x - y
end ActionChoiceInspect
run_elab do
  let env ← Lean.getEnv
  for name in [`ActionChoiceInspect.ordinary, `ActionChoiceInspect.boolean, `ActionChoiceInspect.nested] do
    let some info := env.find? name | throwError "missing"
    Lean.logInfo m!"{name}: {info.value!}"
    Lean.logInfo m!"{repr info.value!}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type info.value!).isSome}"
