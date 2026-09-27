import LeanExe.Extract.ScalarFunc
namespace BooleanStepResultProbe

def saved (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    result

def bound (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag => do
    let result ← pure (ForInStep.yield (flag != (i.toUInt64 == seed)))
    return result

def ignored (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let _unused : ForInStep Bool := .done (!flag)
    .yield (flag != (i.toUInt64 == seed))

def joined (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag => do
    let result ← if i.toUInt64 == seed then pure (ForInStep.done (!flag)) else pure (ForInStep.yield flag)
    return result

end BooleanStepResultProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanStepResultProbe.saved, `BooleanStepResultProbe.bound,
      `BooleanStepResultProbe.ignored, `BooleanStepResultProbe.joined] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
