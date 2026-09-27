import LeanExe.Extract.ScalarFunc

namespace DependentDecisionTest

def dependentReannotatedEq (x y : UInt64) : UInt64 :=
  @dite UInt64
    (@Eq (Id UInt64) ((x + y) % 7) (0))
    (instDecidableEqUInt64 ((x + y) % 7) (0))
    (fun _ => x + 1) (fun _ => y * 3)

def dependentReannotatedOrder (x y : UInt64) : UInt64 :=
  @dite UInt64
    (@GE.ge (Id (Id UInt64)) instLEUInt64 (x >>> y) (y + 1))
    (UInt64.decLe (y + 1) (x >>> y))
    (fun _ => x + 1) (fun _ => y * 3)

def dependentReannotatedCompound (x y : UInt64) : UInt64 :=
  @dite UInt64
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (fun _ => let f := fun z : UInt64 => z + x; f y) (fun _ => y - x)

def dependentReannotatedNested (x y : UInt64) : UInt64 :=
  @dite UInt64
    (@Eq (Id UInt64) ((x + y) % 7) (0))
    (instDecidableEqUInt64 ((x + y) % 7) (0))
    (fun _ => @dite UInt64
    (@GE.ge (Id (Id UInt64)) instLEUInt64 (x >>> y) (y + 1))
    (UInt64.decLe (y + 1) (x >>> y))
    (fun _ => x ^^^ y) (fun _ => x * 7)) (fun _ => @dite UInt64
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (fun _ => x + y) (fun _ => y - x))

def dependentReannotatedHelper (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 =>
    @dite UInt64
      ((@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3)) ∧ (@Ne (Id (Id UInt64)) (z % 5) (0)))
      (@instDecidableAnd (@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3)) (@Ne (Id (Id UInt64)) (z % 5) (0))
        (UInt64.decLt (z + 1) (y * 3)) (@instDecidableNot (@Eq (Id (Id UInt64)) (z % 5) (0)) (instDecidableEqUInt64 (z % 5) (0))))
      (fun _ => z + 1) (fun _ => z * 3)
  f x + f y

def dependentReannotatedDo (x y : UInt64) : UInt64 := Id.run do
  let value ← @dite (Id UInt64)
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)) (instDecidableEqUInt64 ((x + y) % 5) (0))))
    (fun _ => pure (x + 1)) (fun _ => pure (y * 3))
  return value + y

def rangeDependentReannotated (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @dite (Id (ForInStep UInt64))
      (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 11))
      (UInt64.decLe (seed % 11) (UInt64.ofNat i + 1))
      (fun _ => pure (.done (a + UInt64.ofNat i))) (fun _ => pure (.yield (a * 3 + UInt64.ofNat i)))

def rangeDependentReannotatedCompound (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @dite (Id (ForInStep UInt64))
      ((@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) ∧ (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)))
      (@instDecidableAnd (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0))
        (UInt64.decLe (seed % 7) (UInt64.ofNat i + 1)) (@instDecidableNot (@Eq (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 5) (0))))
      (fun _ => let value := a + UInt64.ofNat i; pure (.done value)) (fun _ => let value := a * 3 + UInt64.ofNat i; pure (.yield value))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end DependentDecisionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`DependentDecisionTest.dependentReannotatedEq, DependentDecisionTest.dependentReannotatedEq, false),
    (`DependentDecisionTest.dependentReannotatedOrder, DependentDecisionTest.dependentReannotatedOrder, false),
    (`DependentDecisionTest.dependentReannotatedCompound, DependentDecisionTest.dependentReannotatedCompound, false),
    (`DependentDecisionTest.dependentReannotatedNested, DependentDecisionTest.dependentReannotatedNested, false),
    (`DependentDecisionTest.dependentReannotatedHelper, DependentDecisionTest.dependentReannotatedHelper, false),
    (`DependentDecisionTest.dependentReannotatedDo, DependentDecisionTest.dependentReannotatedDo, false),
    (`DependentDecisionTest.rangeDependentReannotated, DependentDecisionTest.rangeDependentReannotated, true),
    (`DependentDecisionTest.rangeDependentReannotatedCompound, DependentDecisionTest.rangeDependentReannotatedCompound, true)]
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
      else DependentDecisionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 132 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/dependent-decision IR comparisons passed"
