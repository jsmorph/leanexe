import LeanExe.Extract.ScalarFunc

namespace IdComparisonInspect

def equality (x y : UInt64) : UInt64 :=
  if @Eq (Id UInt64) x y then x + 1 else y + 3

def inequality (x y : UInt64) : UInt64 :=
  if @Ne (Id (Id UInt64)) x y then x - y else y + 1

def less (x y : UInt64) : UInt64 :=
  if @LT.lt (Id UInt64) instLTUInt64 x y then x * 3 else y + 7

def atMost (x y : UInt64) : UInt64 :=
  if @LE.le (Id (Id UInt64)) instLEUInt64 x y then x ^^^ y else y / x

def greater (x y : UInt64) : UInt64 :=
  if @GT.gt (Id UInt64) instLTUInt64 x y then x + y else y - x

def atLeast (x y : UInt64) : UInt64 :=
  if @GE.ge (Id (Id UInt64)) instLEUInt64 x y then x % y else y * 7

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if @LT.lt (Id UInt64) instLTUInt64 (UInt64.ofNat i) (seed % 7) then continue
    a := a + UInt64.ofNat i + 1
    if @Eq (Id (Id UInt64)) (a % 5) 0 then break
  return a

end IdComparisonInspect

set_option pp.all true in
run_elab do
  let env ← Lean.getEnv
  for name in [`IdComparisonInspect.equality, `IdComparisonInspect.inequality,
      `IdComparisonInspect.less, `IdComparisonInspect.atMost,
      `IdComparisonInspect.greater, `IdComparisonInspect.atLeast,
      `IdComparisonInspect.range] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {value}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isSome}"

inductive DefaultProbe where
  | eq (n : Nat := 0)

example : DefaultProbe := .eq
