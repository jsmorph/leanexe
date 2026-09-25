import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.Syntax

namespace ResultFunctionTest

def rangeStepJoined (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let result ← if UInt64.ofNat i == seed % 7 then pure (.done (a + 9)) else pure (.yield (a + 1))
    let alias ← pure result
    return alias

def rangeResultFunction (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : ForInStep UInt64 → Id (ForInStep UInt64) := fun result =>
      if a % 3 == 0 then pure (.done (a + seed)) else pure result
    finish (if UInt64.ofNat i == seed % 7 then .done (a + 9) else .yield (a + 1))

def rangeResultChained (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let first : ForInStep UInt64 → ForInStep UInt64 := fun result =>
      if a < 7 then result else .yield (a / 3)
    let second : ForInStep UInt64 → Id (ForInStep UInt64) := fun result =>
      let alias := first result
      if UInt64.ofNat i == 7 then pure (.done (a + 5)) else pure alias
    second (.yield (a * 7 + seed))

def rangeResultCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let captured : ForInStep UInt64 := .done (a + UInt64.ofNat i)
    let finish : ForInStep UInt64 → ForInStep UInt64 := fun result =>
      if a % 5 == seed % 5 then captured else result
    let a := a + 17
    finish (.yield a)

def rangeResultUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _unused : ForInStep UInt64 → Id (ForInStep UInt64) := fun result => pure result
    let ignore : ForInStep UInt64 → ForInStep UInt64 := fun _ => .yield (a + UInt64.ofNat i + 1)
    ignore (.done (a + 99))

def rangeResultWrapped (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : Id (Id (ForInStep UInt64)) → Id (Id (ForInStep UInt64)) := fun result =>
      Id.run do
        let x ← pure (a + UInt64.ofNat i)
        if x % 5 == seed % 5 then return .done (x + 1)
        return result
    finish (pure (.yield (a + 3)))

end ResultFunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`ResultFunctionTest.rangeStepJoined, ResultFunctionTest.rangeStepJoined),
    (`ResultFunctionTest.rangeResultFunction, ResultFunctionTest.rangeResultFunction),
    (`ResultFunctionTest.rangeResultChained, ResultFunctionTest.rangeResultChained),
    (`ResultFunctionTest.rangeResultCapture, ResultFunctionTest.rangeResultCapture),
    (`ResultFunctionTest.rangeResultUnused, ResultFunctionTest.rangeResultUnused),
    (`ResultFunctionTest.rangeResultWrapped, ResultFunctionTest.rangeResultWrapped)]
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
  Lean.logInfo "144 native/result-function IR comparisons passed"
