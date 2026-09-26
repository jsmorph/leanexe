import LeanExe.Extract.ScalarRangeExit
import LeanExe.Extract.Syntax

namespace RangeCountTest

def rangeNatEmpty (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:0] do
    a := a + UInt64.ofNat i + 1
  return a + n

def rangeNatOne (n seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:1] do
    a := a + n + UInt64.ofNat i
  return a

def rangeNatLiteral (limit seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:8] do
    a := a + UInt64.ofNat i
    if UInt64.ofNat i == limit then break
  return a

def rangeNatDirect (limit seed : UInt64) : UInt64 :=
  forIn (m := Id) [:31] seed fun i a =>
    if UInt64.ofNat i == limit then .done (a + 9) else .yield (a * 3 + 1)

def rangeNatMax (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:18446744073709551615] seed fun _ a => .done (a + n)

def tooLarge (seed : UInt64) : UInt64 :=
  forIn (m := Id) [:18446744073709551616] seed fun _ a => .done a

@[instance_reducible] def customNat : OfNat Nat 8 := ⟨9⟩
def customLiteral (seed : UInt64) : UInt64 :=
  forIn (m := Id) [:(@OfNat.ofNat Nat 8 customNat)] seed fun _ a => .done a

end RangeCountTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`RangeCountTest.rangeNatEmpty, RangeCountTest.rangeNatEmpty),
    (`RangeCountTest.rangeNatOne, RangeCountTest.rangeNatOne),
    (`RangeCountTest.rangeNatLiteral, RangeCountTest.rangeNatLiteral),
    (`RangeCountTest.rangeNatDirect, RangeCountTest.rangeNatDirect),
    (`RangeCountTest.rangeNatMax, RangeCountTest.rangeNatMax)]
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some body := LeanExe.Extract.Core.collectLambdas value 2 | throwError "missing parameters"
    let locals : List LeanExe.Extract.Core.ScalarBinding := [.word (.local 1), .word (.local 0)]
    let some plan := LeanExe.Extract.Core.extractScalarRangeExitWith locals 2 body |
      throwError "{name}: literal range extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[plan.func name (some "entry") 2] }
    for limit in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native limit seed
        let actual := module_.evalFunc 0 [limit, seed]
        unless actual == expected do
          throwError "{name}({limit}, {seed}): native={expected}, IR={actual}"
  for name in [`RangeCountTest.tooLarge, `RangeCountTest.customLiteral] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some body := LeanExe.Extract.Core.collectLambdas value 1 | throwError "missing parameters"
    let locals : List LeanExe.Extract.Core.ScalarBinding := [.word (.local 0)]
    unless (LeanExe.Extract.Core.extractScalarRangeExitWith locals 1 body).isNone do
      throwError "{name}: excluded range bound accepted"
  Lean.logInfo "120 native/literal-range IR comparisons and two rejection tests passed"
