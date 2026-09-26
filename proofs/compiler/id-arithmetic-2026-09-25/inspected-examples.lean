import LeanExe.Extract.ScalarFunc
namespace IdArithmeticInspect

def left (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  @HAdd.hAdd (Id UInt64) UInt64 UInt64 (@instHAdd UInt64 instAddUInt64) a y

def right (x y : UInt64) : UInt64 :=
  let b : Id (Id UInt64) := y
  @HSub.hSub UInt64 (Id (Id UInt64)) UInt64 (@instHSub (Id UInt64) instSubUInt64) x b

def both (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  let b : Id (Id UInt64) := y
  @HMul.hMul (Id UInt64) (Id (Id UInt64)) (Id UInt64)
    (@instHMul (Id (Id UInt64)) instMulUInt64) a b

def bitwise (x y : UInt64) : UInt64 :=
  let a : Id (Id UInt64) := x
  let b : Id UInt64 := y
  @HXor.hXor (Id UInt64) (Id (Id UInt64)) UInt64 (@instHXorOfXorOp UInt64 instXorOpUInt64)
    (@HAnd.hAnd (Id (Id UInt64)) (Id UInt64) (Id UInt64)
      (@instHAndOfAndOp (Id UInt64) instAndOpUInt64) a b)
    (@HOr.hOr (Id (Id UInt64)) (Id UInt64) (Id (Id UInt64))
      (@instHOrOfOrOp (Id (Id UInt64)) instOrOpUInt64) a b)

def range (count seed : UInt64) : UInt64 := Id.run do
  let bias : Id UInt64 := seed
  let mut a := seed
  for i in [:count.toNat] do
    let delta : Id (Id UInt64) := UInt64.ofNat i
    let current : Id UInt64 := a
    a := @HAdd.hAdd (Id UInt64) (Id (Id UInt64)) UInt64
      (@instHAdd (Id UInt64) instAddUInt64) current delta
    a := @HAdd.hAdd UInt64 (Id UInt64) UInt64 (@instHAdd UInt64 instAddUInt64) a bias
    if a % 7 == 0 && seed != 0 then break
  return a
end IdArithmeticInspect

set_option pp.all true in
run_elab do
  let env ← Lean.getEnv
  for name in [`IdArithmeticInspect.left, `IdArithmeticInspect.right, `IdArithmeticInspect.both,
      `IdArithmeticInspect.bitwise, `IdArithmeticInspect.range] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {value}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isSome}"
