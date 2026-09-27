import LeanExe.Extract.ScalarEnvironmentFunc
namespace BooleanStepUnitJoinProbe
def unitBooleanJoin (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    let first := if a then seed else i.toUInt64
    if f first (seed + i.toUInt64) then a := !a else a := f seed i.toUInt64
    if f a.toUInt64 first then break
  return a

end BooleanStepUnitJoinProbe
run_elab do
  let env ← Lean.getEnv
  let name := `BooleanStepUnitJoinProbe.unitBooleanJoin
  let some info := env.find? name | throwError "missing"
  let some value := info.value? | throwError "missing"
  Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarEnvironmentFunc env name none info.type value).isSome}"
