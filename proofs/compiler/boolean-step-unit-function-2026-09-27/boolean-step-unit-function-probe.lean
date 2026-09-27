import LeanExe.Extract.ScalarEnvironmentFunc
namespace BooleanStepUnitFunctionProbe

def direct (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f := fun (_u : Unit) (b : Bool) =>
      if i.toUInt64 == seed then ForInStep.done (!b) else ForInStep.yield b
    f () flag

def punit (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f := fun (_u : PUnit.{1}) (b : Bool) =>
      if i.toUInt64 % 3 == seed then ForInStep.done b else ForInStep.yield (!b)
    f PUnit.unit.{1} flag

def retained (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f : Unit → Id Bool → Id (Id (ForInStep Bool)) := fun _u b =>
      pure (pure (if i.toUInt64 == seed then ForInStep.done (!b) else ForInStep.yield b))
    Id.run (Id.run (f () (pure flag)))

def capture (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f := fun (_u : Unit) (b : Bool) =>
      if i.toUInt64 == seed then ForInStep.done (b != flag) else ForInStep.yield b
    f () (!flag)

def nested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let f := fun (_u : Unit) (b : Bool) =>
      if i.toUInt64 == seed then ForInStep.done (!b) else ForInStep.yield b
    let g := fun (_u : PUnit.{1}) (b : Bool) => f () (b != flag)
    g PUnit.unit.{1} flag

def unused (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed != 0) fun i flag =>
    let _f := fun (_u : Unit) (b : Bool) =>
      if i.toUInt64 == seed then ForInStep.done (!b) else ForInStep.yield b
    ForInStep.yield (!flag)

end BooleanStepUnitFunctionProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanStepUnitFunctionProbe.direct, `BooleanStepUnitFunctionProbe.punit,
      `BooleanStepUnitFunctionProbe.retained, `BooleanStepUnitFunctionProbe.capture,
      `BooleanStepUnitFunctionProbe.nested, `BooleanStepUnitFunctionProbe.unused] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarEnvironmentFunc env name none info.type value).isSome}"
