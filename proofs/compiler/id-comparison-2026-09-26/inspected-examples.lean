import LeanExe.Extract.ScalarFunc

namespace IdComparisonInspect

def equality (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq (Id UInt64) x y) (instDecidableEqUInt64 x y) (x + 1) (y + 3)

def inequality (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Ne (Id (Id UInt64)) x y)
    (@instDecidableNot (@Eq (Id (Id UInt64)) x y) (instDecidableEqUInt64 x y)) (x - y) (y + 1)

def less (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LT.lt (Id UInt64) instLTUInt64 x y) (UInt64.decLt x y) (x * 3) (y + 7)

def atMost (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LE.le (Id (Id UInt64)) instLEUInt64 x y) (UInt64.decLe x y) (x ^^^ y) (y / x)

def greater (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GT.gt (Id UInt64) instLTUInt64 x y) (UInt64.decLt y x) (x + y) (y - x)

def atLeast (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GE.ge (Id (Id UInt64)) instLEUInt64 x y) (UInt64.decLe y x) (x % y) (y * 7)

def range (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      (@LT.lt (Id UInt64) instLTUInt64 (UInt64.ofNat i) (seed % 7))
      (UInt64.decLt (UInt64.ofNat i) (seed % 7))
      (pure (.yield a))
      (@ite (Id (ForInStep UInt64))
        (@Eq (Id (Id UInt64)) ((a + UInt64.ofNat i + 1) % 5) 0)
        (instDecidableEqUInt64 ((a + UInt64.ofNat i + 1) % 5) 0)
        (pure (.done (a + UInt64.ofNat i + 1)))
        (pure (.yield (a + UInt64.ofNat i + 1))))

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
