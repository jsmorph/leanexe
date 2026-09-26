import LeanExe.Extract.ScalarFunc

namespace IdComparisonTest

def idComparisonEq (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq (Id UInt64) x y) (instDecidableEqUInt64 x y) (x + 1) (y + 3)

def idComparisonNe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Ne (Id (Id UInt64)) x y)
    (@instDecidableNot (@Eq (Id (Id UInt64)) x y) (instDecidableEqUInt64 x y)) (x - y) (y + 1)

def idComparisonLt (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LT.lt (Id UInt64) instLTUInt64 x y) (UInt64.decLt x y) (x * 3) (y + 7)

def idComparisonLe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LE.le (Id (Id UInt64)) instLEUInt64 x y) (UInt64.decLe x y) (x ^^^ y) (y / x)

def idComparisonGt (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GT.gt (Id UInt64) instLTUInt64 x y) (UInt64.decLt y x) (x + y) (y - x)

def idComparisonGe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GE.ge (Id (Id UInt64)) instLEUInt64 x y) (UInt64.decLe y x) (x % y) (y * 7)

def rangeIdComparisonExit (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      (@LT.lt (Id UInt64) instLTUInt64 (UInt64.ofNat i) (seed % 7 : UInt64))
      (UInt64.decLt (UInt64.ofNat i) (seed % 7))
      (pure (.yield a))
      (@ite (Id (ForInStep UInt64))
        (@Eq (Id (Id UInt64)) ((a + UInt64.ofNat i + 1) % 5 : UInt64) (0 : UInt64))
        (instDecidableEqUInt64 ((a + UInt64.ofNat i + 1) % 5) 0)
        (pure (.done (a + UInt64.ofNat i + 1)))
        (pure (.yield (a + UInt64.ofNat i + 1))))

def idComparisonNegated (x y : UInt64) : UInt64 :=
  @ite UInt64 (Not (@LE.le (Id (Id (Id UInt64))) instLEUInt64 x y))
    (@instDecidableNot (@LE.le (Id (Id (Id UInt64))) instLEUInt64 x y) (UInt64.decLe x y))
    (x + 11) (y - 13)

def idComparisonCompound (x y : UInt64) : UInt64 :=
  @ite UInt64 ((@Eq (Id UInt64) x y) ∨ (@LT.lt (Id (Id UInt64)) instLTUInt64 x y))
    (@instDecidableOr (@Eq (Id UInt64) x y) (@LT.lt (Id (Id UInt64)) instLTUInt64 x y)
      (instDecidableEqUInt64 x y) (UInt64.decLt x y)) (x * 3) (y / x)

def idComparisonDependent (x y : UInt64) : UInt64 :=
  @dite UInt64 (@Eq (Id (Id UInt64)) x y) (instDecidableEqUInt64 x y)
    (fun _ => let f := fun z : UInt64 => z + x; f y)
    (fun _ => y - x)

def idComparisonDecide (x y : UInt64) : UInt64 :=
  let flag := @decide (@GE.ge (Id UInt64) instLEUInt64 x y) (UInt64.decLe y x)
  if flag then x + 17 else y + 19

def idComparisonChoice (x y : UInt64) : UInt64 :=
  let flag := @ite Bool (@Eq (Id UInt64) x y) (instDecidableEqUInt64 x y) (x != 0) (y == 0)
  if flag then x ^^^ y else x * 7

def idComparisonDo (x y : UInt64) : UInt64 := Id.run do
  let f := fun z : UInt64 =>
    @ite UInt64 (@LT.lt (Id UInt64) instLTUInt64 z y) (UInt64.decLt z y) (z + 1) (z * 3)
  let value ← @ite (Id UInt64) (@Eq (Id (Id UInt64)) x y) (instDecidableEqUInt64 x y)
    (pure (f x)) (pure (f (x + y)))
  return value + f y

def rangeIdComparisonDecide (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := @decide (@LT.lt (Id (Id UInt64)) instLTUInt64 (UInt64.ofNat i) (seed % 7 : UInt64))
      (UInt64.decLt (UInt64.ofNat i) (seed % 7))
    if flag then continue
    a := a + UInt64.ofNat i + 1
    if a % 5 == 0 then break
  return a

def rangeIdComparisonDependent (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @dite (Id (ForInStep UInt64)) (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i) (seed % 11 : UInt64))
      (UInt64.decLe (seed % 11) (UInt64.ofNat i))
      (fun _ => pure (.done (a + UInt64.ofNat i)))
      (fun _ => pure (.yield (a * 3 + UInt64.ofNat i)))

def idComparisonCustomDecision (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq (Id UInt64) x y) ((fun d : Decidable (x = y) => d) (instDecidableEqUInt64 x y)) (x + 1) (y + 3)

def idComparisonCustomOrder (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LT.lt (Id UInt64) { lt := fun a b => a = b } x y)
    (instDecidableEqUInt64 x y) (x + 1) (y + 3)

def idComparisonUnsupported (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq (Id UInt64) (UInt64.ofNat (toString x).length) y)
    (instDecidableEqUInt64 (UInt64.ofNat (toString x).length) y) (x + 1) (y + 3)

def rangeIdComparisonUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64)) (@Eq (Id UInt64) (UInt64.ofNat (toString i).length) a)
      (instDecidableEqUInt64 (UInt64.ofNat (toString i).length) a)
      (pure (.done a)) (pure (.yield (a + 1)))

def rangeIdComparisonEvidenceAnnotations (count seed : UInt64) : UInt64 :=
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


def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end IdComparisonTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`IdComparisonTest.idComparisonEq, IdComparisonTest.idComparisonEq, false),
    (`IdComparisonTest.idComparisonNe, IdComparisonTest.idComparisonNe, false),
    (`IdComparisonTest.idComparisonLt, IdComparisonTest.idComparisonLt, false),
    (`IdComparisonTest.idComparisonLe, IdComparisonTest.idComparisonLe, false),
    (`IdComparisonTest.idComparisonGt, IdComparisonTest.idComparisonGt, false),
    (`IdComparisonTest.idComparisonGe, IdComparisonTest.idComparisonGe, false),
    (`IdComparisonTest.rangeIdComparisonEvidenceAnnotations, IdComparisonTest.rangeIdComparisonEvidenceAnnotations, true),
    (`IdComparisonTest.rangeIdComparisonExit, IdComparisonTest.rangeIdComparisonExit, true),
    (`IdComparisonTest.idComparisonNegated, IdComparisonTest.idComparisonNegated, false),
    (`IdComparisonTest.idComparisonCompound, IdComparisonTest.idComparisonCompound, false),
    (`IdComparisonTest.idComparisonDependent, IdComparisonTest.idComparisonDependent, false),
    (`IdComparisonTest.idComparisonDecide, IdComparisonTest.idComparisonDecide, false),
    (`IdComparisonTest.idComparisonChoice, IdComparisonTest.idComparisonChoice, false),
    (`IdComparisonTest.idComparisonDo, IdComparisonTest.idComparisonDo, false),
    (`IdComparisonTest.rangeIdComparisonDecide, IdComparisonTest.rangeIdComparisonDecide, true),
    (`IdComparisonTest.rangeIdComparisonDependent, IdComparisonTest.rangeIdComparisonDependent, true)]
  let mut count : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Id-annotated comparison extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else IdComparisonTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      count := count + 1
  for name in [
    `IdComparisonTest.idComparisonCustomDecision,
    `IdComparisonTest.idComparisonCustomOrder,
    `IdComparisonTest.idComparisonUnsupported,
    `IdComparisonTest.rangeIdComparisonUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported comparison accepted"
  unless count == 264 do throwError "wrong comparison count {count}"
  Lean.logInfo m!"{count} native/Id-comparison IR comparisons and four declaration rejection tests passed"
