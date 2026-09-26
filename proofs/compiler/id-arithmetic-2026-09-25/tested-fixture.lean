import LeanExe.Extract.ScalarFunc

namespace IdArithmeticTest

def idArithmeticLeft (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  @HAdd.hAdd (Id UInt64) UInt64 UInt64 (@instHAdd UInt64 instAddUInt64) a y

def idArithmeticRight (x y : UInt64) : UInt64 :=
  let b : Id (Id UInt64) := y
  @HSub.hSub UInt64 (Id (Id UInt64)) UInt64 (@instHSub (Id UInt64) instSubUInt64) x b

def idArithmeticBoth (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  let b : Id (Id UInt64) := y
  @HMul.hMul (Id UInt64) (Id (Id UInt64)) (Id UInt64)
    (@instHMul (Id (Id UInt64)) instMulUInt64) a b

def idArithmeticBitwise (x y : UInt64) : UInt64 :=
  let a : Id (Id UInt64) := x
  let b : Id UInt64 := y
  @HXor.hXor (Id UInt64) (Id (Id UInt64)) UInt64 (@instHXorOfXorOp UInt64 instXorOpUInt64)
    (@HAnd.hAnd (Id (Id UInt64)) (Id UInt64) (Id UInt64)
      (@instHAndOfAndOp (Id UInt64) instAndOpUInt64) a b)
    (@HOr.hOr (Id (Id UInt64)) (Id UInt64) (Id (Id UInt64))
      (@instHOrOfOrOp (Id (Id UInt64)) instOrOpUInt64) a b)

def idArithmeticDivision (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := x
  let b : Id (Id UInt64) := y
  @HDiv.hDiv (Id UInt64) (Id (Id UInt64)) UInt64
    (@instHDiv (Id UInt64) instDivUInt64) a b +
  @HMod.hMod (Id UInt64) (Id (Id UInt64)) UInt64
    (@instHMod (Id (Id UInt64)) instModUInt64) a b

def idArithmeticShifts (x y : UInt64) : UInt64 :=
  let a : Id (Id UInt64) := x
  let b : Id UInt64 := y
  @HShiftLeft.hShiftLeft (Id (Id UInt64)) (Id UInt64) UInt64
    (@instHShiftLeftOfShiftLeft (Id UInt64) instShiftLeftUInt64) a b ^^^
  @HShiftRight.hShiftRight (Id (Id UInt64)) (Id UInt64) UInt64
    (@instHShiftRightOfShiftRight (Id (Id UInt64)) instShiftRightUInt64) a b

def idArithmeticHelper (x y : UInt64) : UInt64 :=
  let a : Id (Id UInt64) := x
  let f := fun z : UInt64 =>
    (@HAdd.hAdd (Id (Id UInt64)) UInt64 UInt64
      (@instHAdd (Id UInt64) instAddUInt64) a z != 0).toUInt64
  if f y != 0 then f (x + y) + y else x

def idArithmeticDo (x y : UInt64) : UInt64 := Id.run do
  let a : Id UInt64 := x
  let value ← pure (@HAdd.hAdd (Id UInt64) UInt64 UInt64
    (@instHAdd (Id (Id UInt64)) instAddUInt64) a y)
  let b : Id (Id UInt64) := value
  let next : Id UInt64 := @HMul.hMul (Id (Id UInt64)) (Id UInt64) (Id UInt64)
    (@instHMul (Id UInt64) instMulUInt64) b a
  return Id.run next

def rangeIdArithmeticYield (count seed : UInt64) : UInt64 := Id.run do
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
def rangeIdArithmeticContinue (count seed : UInt64) : UInt64 := Id.run do
  let bias : Id (Id UInt64) := seed
  let mut a := seed
  for i in [:count.toNat] do
    let index : Id UInt64 := UInt64.ofNat i
    let value := @HAdd.hAdd (Id UInt64) (Id (Id UInt64)) UInt64
      (@instHAdd (Id UInt64) instAddUInt64) index bias
    if value % 3 == 1 then continue
    let current : Id UInt64 := a
    a := @HAdd.hAdd (Id UInt64) UInt64 UInt64
      (@instHAdd (Id (Id UInt64)) instAddUInt64) current value
    if a % 7 == 0 && seed != 0 then break
  return a

def rangeIdArithmeticBounds (count seed : UInt64) : UInt64 :=
  let limit : Id UInt64 := count
  let stop := @HAdd.hAdd (Id UInt64) UInt64 UInt64
    (@instHAdd (Id (Id UInt64)) instAddUInt64) limit 1
  let value : Id (Id UInt64) := Id.run do
    let mut a := seed
    for i in [1:stop.toNat:2] do
      let index : Id UInt64 := UInt64.ofNat i
      a := @HAdd.hAdd UInt64 (Id UInt64) UInt64
        (@instHAdd (Id UInt64) instAddUInt64) a index
      if a % 7 == 0 && seed != 0 then break
    return a
  @HAdd.hAdd (Id (Id UInt64)) UInt64 UInt64 (@instHAdd UInt64 instAddUInt64) value seed

def rangeIdArithmeticStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let current : Id (Id UInt64) := a
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let value := @HAdd.hAdd (Id (Id UInt64)) UInt64 UInt64
        (@instHAdd (Id UInt64) instAddUInt64) current (UInt64.ofNat i)
      if _h : flag then return .done value
      else return .yield (value + 1)
    f (a % 7 == 0 && seed != 0)

def idArithmeticCustom (x y : UInt64) : UInt64 :=
  @HAdd.hAdd (Id UInt64) UInt64 UInt64
    { hAdd := fun a b => Id.run a + b + 1 } x y

def idArithmeticUnsupported (x y : UInt64) : UInt64 :=
  let a : Id UInt64 := UInt64.ofNat (toString x).length
  @HAdd.hAdd (Id UInt64) UInt64 UInt64 (@instHAdd UInt64 instAddUInt64) a y

def idArithmeticNat (x y : UInt64) : UInt64 :=
  let a : Id Nat := x.toNat
  UInt64.ofNat (@HAdd.hAdd (Id Nat) Nat Nat (@instHAdd Nat instAddNat) a y.toNat)

def rangeIdArithmeticCustom (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    return .yield (@HAdd.hAdd (Id UInt64) UInt64 UInt64
      { hAdd := fun a b => Id.run a + b + 1 } a (UInt64.ofNat i))
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end IdArithmeticTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`IdArithmeticTest.idArithmeticLeft, IdArithmeticTest.idArithmeticLeft, false),
    (`IdArithmeticTest.idArithmeticRight, IdArithmeticTest.idArithmeticRight, false),
    (`IdArithmeticTest.idArithmeticBoth, IdArithmeticTest.idArithmeticBoth, false),
    (`IdArithmeticTest.idArithmeticBitwise, IdArithmeticTest.idArithmeticBitwise, false),
    (`IdArithmeticTest.idArithmeticDivision, IdArithmeticTest.idArithmeticDivision, false),
    (`IdArithmeticTest.idArithmeticShifts, IdArithmeticTest.idArithmeticShifts, false),
    (`IdArithmeticTest.idArithmeticHelper, IdArithmeticTest.idArithmeticHelper, false),
    (`IdArithmeticTest.idArithmeticDo, IdArithmeticTest.idArithmeticDo, false),
    (`IdArithmeticTest.rangeIdArithmeticYield, IdArithmeticTest.rangeIdArithmeticYield, true),
    (`IdArithmeticTest.rangeIdArithmeticContinue, IdArithmeticTest.rangeIdArithmeticContinue, true),
    (`IdArithmeticTest.rangeIdArithmeticBounds, IdArithmeticTest.rangeIdArithmeticBounds, true),
    (`IdArithmeticTest.rangeIdArithmeticStep, IdArithmeticTest.rangeIdArithmeticStep, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Id-annotated arithmetic extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else IdArithmeticTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`IdArithmeticTest.idArithmeticCustom, `IdArithmeticTest.idArithmeticUnsupported, `IdArithmeticTest.idArithmeticNat, `IdArithmeticTest.rangeIdArithmeticCustom] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Id-annotated arithmetic accepted"
  Lean.logInfo "208 native/Id-arithmetic IR comparisons and four declaration rejection tests passed"
