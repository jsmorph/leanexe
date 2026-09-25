import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.Syntax

namespace StepResultTest

def rangeStepRun (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => Id.run do
    let x ← pure (a + UInt64.ofNat i)
    if x % 5 == seed % 5 then return .done (x + 7)
    return .yield (x * 3 + 1)

def rangeStepPure (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    pure (if UInt64.ofNat i == seed % 7 then .done (a + 9) else .yield (a + 1))

def rangeStepLet (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let result : ForInStep UInt64 :=
      if UInt64.ofNat i == seed % 3 then .done (a + 7) else .yield (a + UInt64.ofNat i)
    let alias := result
    pure alias

def rangeStepCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let result : ForInStep UInt64 :=
      if a % 5 == seed % 5 then .done (a + 3) else .yield (a + UInt64.ofNat i)
    let finish : UInt64 → Id (ForInStep UInt64) := fun x =>
      if x < 7 then pure result else pure (.yield (x + 1))
    finish (a + 1)

def rangeStepBind (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let result ← if UInt64.ofNat i == seed % 7 then pure (.done (a + 9)) else pure (.yield (a + 1))
    let alias ← pure result
    return alias

def rangeStepIdLet (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let result : Id (ForInStep UInt64) := do
      let x ← pure (a + UInt64.ofNat i)
      if x % 7 == seed % 7 then return .done (x + 1)
      return .yield (x * 3)
    result

def rangeStepUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let _ignored ← pure (ForInStep.done (a + 99))
    let result : ForInStep UInt64 := .yield (a + UInt64.ofNat i + 1)
    return result

end StepResultTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`StepResultTest.rangeStepRun, StepResultTest.rangeStepRun),
    (`StepResultTest.rangeStepPure, StepResultTest.rangeStepPure),
    (`StepResultTest.rangeStepLet, StepResultTest.rangeStepLet),
    (`StepResultTest.rangeStepCapture, StepResultTest.rangeStepCapture),
    (`StepResultTest.rangeStepBind, StepResultTest.rangeStepBind),
    (`StepResultTest.rangeStepIdLet, StepResultTest.rangeStepIdLet),
    (`StepResultTest.rangeStepUnused, StepResultTest.rangeStepUnused)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some body := LeanExe.Extract.Core.collectLambdas value 2 | throwError "missing parameters"
    let locals : List LeanExe.Extract.Core.ScalarBinding := [.word (.local 1), .word (.local 0)]
    let some plan := LeanExe.Extract.Core.extractScalarRangeExitWith locals 2 body |
      throwError "{name}: step-result extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[plan.func name (some "entry") 2] }
    for limit in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native limit seed
        let actual := module_.evalFunc 0 [limit, seed]
        unless actual == expected do
          throwError "{name}({limit}, {seed}): native={expected}, IR={actual}"
  Lean.logInfo "168 native/step-result IR comparisons passed"
