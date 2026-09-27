import LeanExe.Extract.ScalarFunc
namespace BooleanStepFunctionProbe

def word (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => if n % 3 == 0 then ForInStep.done (!flag) else .yield flag
    f (i.toUInt64 + seed)

def boolean (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun b : Bool => if b then ForInStep.done (!flag) else .yield flag
    f (i.toUInt64 == seed)

def nested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => if n % 3 == 0 then ForInStep.done (!flag) else .yield flag
    let g := fun b : Bool => if b then f i.toUInt64 else f seed
    g (i.toUInt64 == seed)

def retained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let f := fun n : Id UInt64 => (show Id (ForInStep Bool) from pure (ForInStep.yield (flag != (Id.run n == seed))))
    Id.run (f (pure i.toUInt64))

end BooleanStepFunctionProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanStepFunctionProbe.word, `BooleanStepFunctionProbe.boolean,
      `BooleanStepFunctionProbe.nested, `BooleanStepFunctionProbe.retained] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
