import LeanExe.Extract.ScalarFunc
namespace BooleanStepMatchProbe

def direct (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    ForInStep.casesOn (motive := fun _ => ForInStep Bool) result
      (fun value => .yield value) (fun value => .done value)

def matched (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .yield value
    | .yield value => .done value

def helper (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool =>
      ForInStep.casesOn (motive := fun _ => ForInStep Bool) result
        (fun value => if i.toUInt64 == seed then .done (!value) else .yield flag)
        (fun value => .yield (value != flag))
    f (if flag then .done false else .yield true)

def retained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    ForInStep.casesOn (motive := fun _ => Id (ForInStep Bool))
      (if i.toUInt64 == seed then .done (!flag) else .yield flag)
      (fun value => pure (ForInStep.yield value))
      (fun value => pure (ForInStep.done value))

end BooleanStepMatchProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanStepMatchProbe.direct, `BooleanStepMatchProbe.matched,
      `BooleanStepMatchProbe.helper, `BooleanStepMatchProbe.retained] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
