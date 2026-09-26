import LeanExe.Extract.ScalarStep
import LeanExe.Extract.Syntax
import LeanExe.IR.ScalarRangeExitSlots

namespace RangeExitTest

def early (i : Nat) (a _seed : UInt64) : Id (ForInStep UInt64) := do
  if a % 7 == UInt64.ofNat i then return .done (a + 11)
  return .yield (a + 3)

def updated (i : Nat) (a _seed : UInt64) : Id (ForInStep UInt64) := do
  let next := a + UInt64.ofNat i
  if next < 7 then return .done next
  return .yield (next * 3)

def joined (i : Nat) (a seed : UInt64) : Id (ForInStep UInt64) := do
  let index := UInt64.ofNat i
  let delta ← if a < seed then pure (a + index) else pure (seed / index)
  if delta == 0 then return .done (a + 1)
  return .yield (a + delta)

def localStep (i : Nat) (a seed : UInt64) : Id (ForInStep UInt64) :=
  let finish := fun x : UInt64 =>
    if x % 3 == 0 then pure (.done (x + seed)) else pure (.yield (x + UInt64.ofNat i))
  finish a

def unitStep (i : Nat) (a seed : UInt64) : Id (ForInStep UInt64) :=
  let finish := fun (_ : Unit) (x : UInt64) =>
    if x == seed then pure (.done (x + 1)) else pure (.yield (x + UInt64.ofNat i))
  finish () (a + UInt64.ofNat i)

end RangeExitTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (Nat → UInt64 → UInt64 → ForInStep UInt64)) := [
    (`RangeExitTest.early, RangeExitTest.early), (`RangeExitTest.updated, RangeExitTest.updated),
    (`RangeExitTest.joined, RangeExitTest.joined), (`RangeExitTest.localStep, RangeExitTest.localStep),
    (`RangeExitTest.unitStep, RangeExitTest.unitStep)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some body := LeanExe.Extract.Core.collectLambdas value 3 | throwError "missing parameters"
    let locals : List LeanExe.Extract.Core.ScalarStepBinding := [
      .scalar (.word (.local 1)), .scalar (.word (.local 2)), .scalar (.natural (.local 3))]
    let some code := LeanExe.Extract.Core.extractScalarStepWith locals body |
      throwError "{name}: step extraction failed"
    let func : LeanExe.IR.Func :=
      { sourceName := name, exportName := some "step", params := 2, locals := 6
        body := .seq (.assign 4 (.local 0))
          (.seq (.assign 2 (.local 1))
            (.seq (.assign 3 (.u64 0))
              (.seq (.assign 5 (.u64 0))
                (.while (LeanExe.IR.rangeCondition 2) (LeanExe.IR.rangeExitBody 2 code.value code.done)))))
        results := [.local 2] }
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := forIn (m := Id) [:count.toNat] seed (fun i a => native i a seed)
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do
          throwError "{name}({count}, {seed}): native={expected}, IR={actual}"
  Lean.logInfo "120 native/range-exit IR comparisons passed"
