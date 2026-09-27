import LeanExe.Extract.ScalarFunc
namespace BooleanStepScalarFunctionProbe

def word (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => n + seed
    if f i.toUInt64 == 0 then .done (!flag) else .yield flag

def predicate (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun n : UInt64 => n % 3 == seed
    if f i.toUInt64 then .done (!flag) else .yield flag

def booleanWord (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun b : Bool => if b then seed + 1 else seed * 3
    if f flag == i.toUInt64 then .done (!flag) else .yield flag

def booleanPredicate (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun b : Bool => b != (i.toUInt64 == seed)
    .yield (f flag)

end BooleanStepScalarFunctionProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanStepScalarFunctionProbe.word, `BooleanStepScalarFunctionProbe.predicate,
      `BooleanStepScalarFunctionProbe.booleanWord, `BooleanStepScalarFunctionProbe.booleanPredicate] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
