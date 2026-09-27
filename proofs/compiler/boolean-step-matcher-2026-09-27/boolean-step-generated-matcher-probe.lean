import LeanExe.Extract.Arithmetic
namespace BooleanStepMatcherEnvironmentProbe

def direct (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .yield value
    | .yield value => .done value

def helper (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool =>
      match result with
      | .done value => if i.toUInt64 == seed then .done (!value) else .yield flag
      | .yield value => .yield (value != flag)
    f (if flag then .done false else .yield true)

def nested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value =>
      let inner : ForInStep Bool := .yield (!value)
      match inner with
      | .done value => .done (value != flag)
      | .yield value => .yield value
    | .yield value => .yield (value != flag)

def retained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => pure (ForInStep.yield value)
    | .yield value => pure (ForInStep.done value)

end BooleanStepMatcherEnvironmentProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanStepMatcherEnvironmentProbe.direct, `BooleanStepMatcherEnvironmentProbe.helper,
      `BooleanStepMatcherEnvironmentProbe.nested, `BooleanStepMatcherEnvironmentProbe.retained] do
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Arithmetic.compileEnvironment env `BooleanStepMatcherEnvironmentProbe name).isOk}"
