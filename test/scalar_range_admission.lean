import LeanExe.Extract.ScalarRangeSyntax
import LeanExe.Extract.ScalarRange
import LeanExe.Extract.Syntax

namespace RangeAdmission

def indexed (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    a := a + UInt64.ofNat i
  return a

def indexFree (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for _ in [:n.toNat] do
    a := a + 3
  return a

def changedStep (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [0:n.toNat:2] do
    a := a + UInt64.ofNat i
  return a

def breaks (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:n.toNat] do
    if i == 2 then break
    a := a + 3
  return a

def beforeAfter (n seed : UInt64) : UInt64 := Id.run do
  let offset := seed * 3
  let count ← pure (n % 17)
  let mut a := offset
  for i in [:count.toNat] do
    a := if a < 7 then a + UInt64.ofNat i else (a * 3) ^^^ UInt64.ofNat i
  return a + offset

end RangeAdmission

run_elab do
  let env ← Lean.getEnv
  for (name, expectedRange, expectedStep) in [
      (`RangeAdmission.indexed, true, true),
      (`RangeAdmission.indexFree, true, true),
      (`RangeAdmission.changedStep, false, false),
      (`RangeAdmission.breaks, true, false)] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some call := value.find? (fun e => e.getAppFn.isConstOf ``ForIn.forIn && e.getAppNumArgs == 8) |
      throwError "missing range iterator in {name}"
    let view := LeanExe.Extract.Core.scalarRange? call
    unless view.isSome == expectedRange do
      throwError "{name}: iterator recognition mismatch"
    if let some view := view then
      let step := LeanExe.Extract.Core.scalarYield? view.body
      unless step.isSome == expectedStep do
        throwError "{name}: yield recognition mismatch"
      if let some step := step then
        let locals := [LeanExe.Extract.Core.ScalarBinding.word (.local 2), .natural (.local 3),
          .word (.local 2), .word (.local 1), .word (.local 0)]
        unless (LeanExe.Extract.Core.extractScalarExprWith locals step).isSome do
          throwError "{name}: scalar step extraction failed"
  Lean.logInfo "range syntax and typed step admission passed"

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`RangeAdmission.indexed, RangeAdmission.indexed),
    (`RangeAdmission.indexFree, RangeAdmission.indexFree),
    (`RangeAdmission.beforeAfter, RangeAdmission.beforeAfter)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some body := LeanExe.Extract.Core.collectLambdas value 2 | throwError "missing parameters"
    let some plan := LeanExe.Extract.Core.extractScalarRangeWith [.word (.local 1), .word (.local 0)] 2 body |
      throwError "{name}: whole loop extraction failed"
    let emittedModule : LeanExe.IR.Module := { funcs := #[plan.func name (some "range") 2] }
    for count in [0, 1, 2, 7, 16] do
      for seed in [0, 1, 18446744073709551615] do
        let actual := emittedModule.evalFunc 0 [count, seed]
        let expected := native count seed
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, extracted={actual}"
  Lean.logInfo "45 native/range-IR comparisons passed"
