import LeanExe.Extract.ScalarFunc
namespace BooleanStepResultFunctionProbe

def direct (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool => result
    f (if i.toUInt64 == seed then .done (!flag) else .yield flag)

def ignored (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun _result : ForInStep Bool => ForInStep.yield (flag != (i.toUInt64 == seed))
    f (.done (!flag))

def nested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool => if flag then result else ForInStep.yield true
    let g := fun result : ForInStep Bool => f result
    g (if i.toUInt64 == seed then .done (!flag) else .yield flag)

def retained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let f : Id (ForInStep Bool) → Id (Id (ForInStep Bool)) := fun result => pure result
    Id.run (Id.run (f (pure (ForInStep.yield (flag != (i.toUInt64 == seed))))))

end BooleanStepResultFunctionProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanStepResultFunctionProbe.direct, `BooleanStepResultFunctionProbe.ignored,
      `BooleanStepResultFunctionProbe.nested, `BooleanStepResultFunctionProbe.retained] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
