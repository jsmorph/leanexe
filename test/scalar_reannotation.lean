import LeanExe.Extract.ScalarFunc

namespace ReannotationTest

def reannotatedEq (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Eq (Id UInt64) ((x + y) % 7) 0)
    (instDecidableEqUInt64 ((x + y) % 7) 0) (x + 1) (y + 3)

def reannotatedNe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@Ne (Id (Id UInt64)) (x - y) (y * 3))
    (@instDecidableNot (@Eq (Id (Id UInt64)) (x - y) (y * 3))
      (instDecidableEqUInt64 (x - y) (y * 3))) (x - y) (y + 1)

def reannotatedLt (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LT.lt (Id UInt64) instLTUInt64 (x / y) (y % 7))
    (UInt64.decLt (x / y) (y % 7)) (x * 3) (y + 7)

def reannotatedLe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@LE.le (Id (Id UInt64)) instLEUInt64 (x &&& y) (y ||| 3))
    (UInt64.decLe (x &&& y) (y ||| 3)) (x ^^^ y) (y / x)

def reannotatedGt (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GT.gt (Id UInt64) instLTUInt64 (x <<< y) (y ^^^ 5))
    (UInt64.decLt (y ^^^ 5) (x <<< y)) (x + y) (y - x)

def reannotatedGe (x y : UInt64) : UInt64 :=
  @ite UInt64 (@GE.ge (Id (Id UInt64)) instLEUInt64 (x >>> y) (y * 7))
    (UInt64.decLe (y * 7) (x >>> y)) (x % y) (y * 7)

def reannotatedNegated (x y : UInt64) : UInt64 :=
  @ite UInt64 (Not (Not (@LE.le (Id UInt64) instLEUInt64 (x + 1) (y * 7))))
    (@instDecidableNot (Not (@LE.le (Id UInt64) instLEUInt64 (x + 1) (y * 7)))
      (@instDecidableNot (@LE.le (Id UInt64) instLEUInt64 (x + 1) (y * 7))
        (UInt64.decLe (x + 1) (y * 7)))) (x + 11) (y - 13)

def reannotatedHelper (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 =>
    @ite UInt64 (@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3))
      (UInt64.decLt (z + 1) (y * 3)) (z + 1) (z * 3)
  f x + f y

def reannotatedDo (x y : UInt64) : UInt64 := Id.run do
  let value ← @ite (Id UInt64) (@Eq (Id (Id UInt64)) ((x + y) % 7) 0)
    (instDecidableEqUInt64 ((x + y) % 7) 0) (pure (x + 1)) (pure (y * 3))
  return value + y

def rangeReannotatedOrder (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 11))
      (UInt64.decLe (seed % 11) (UInt64.ofNat i + 1))
      (pure (.done (a + UInt64.ofNat i)))
      (pure (.yield (a * 3 + UInt64.ofNat i)))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end ReannotationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`ReannotationTest.reannotatedEq, ReannotationTest.reannotatedEq, false),
    (`ReannotationTest.reannotatedNe, ReannotationTest.reannotatedNe, false),
    (`ReannotationTest.reannotatedLt, ReannotationTest.reannotatedLt, false),
    (`ReannotationTest.reannotatedLe, ReannotationTest.reannotatedLe, false),
    (`ReannotationTest.reannotatedGt, ReannotationTest.reannotatedGt, false),
    (`ReannotationTest.reannotatedGe, ReannotationTest.reannotatedGe, false),
    (`ReannotationTest.reannotatedNegated, ReannotationTest.reannotatedNegated, false),
    (`ReannotationTest.reannotatedHelper, ReannotationTest.reannotatedHelper, false),
    (`ReannotationTest.reannotatedDo, ReannotationTest.reannotatedDo, false),
    (`ReannotationTest.rangeReannotatedOrder, ReannotationTest.rangeReannotatedOrder, true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reannotated comparison extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else ReannotationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 150 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/reannotated-comparison IR comparisons passed"
