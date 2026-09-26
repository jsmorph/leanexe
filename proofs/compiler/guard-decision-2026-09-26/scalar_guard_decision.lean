import LeanExe.Extract.ScalarFunc

namespace GuardDecisionTest

def reannotatedAnd (x y : UInt64) : UInt64 :=
  @ite UInt64
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableAnd (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (instDecidableEqUInt64 ((x + y) % 5) (0)))
    (x + 1) (y * 3)

def reannotatedOr (x y : UInt64) : UInt64 :=
  @ite UInt64
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3)))
    (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3))
      (UInt64.decLt (x + 1) (y * 7)) (@instDecidableNot (@Eq (Id (Id UInt64)) (x ^^^ y) (y + 3)) (instDecidableEqUInt64 (x ^^^ y) (y + 3))))
    (x + 1) (y * 3)

def reannotatedGuardNegation (x y : UInt64) : UInt64 :=
  @ite UInt64
    (Not (Not ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)))))
    (@instDecidableNot (Not ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)))) (@instDecidableNot ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))) (@instDecidableAnd (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (instDecidableEqUInt64 ((x + y) % 5) (0)))))
    (x + 1) (y * 3)

def reannotatedNestedGuard (x y : UInt64) : UInt64 :=
  @ite UInt64
    (((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))) ∧ (Not (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3))))
    (@instDecidableAnd ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∨ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))) (Not (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3)))
      (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (instDecidableEqUInt64 ((x + y) % 5) (0))) (@instDecidableNot (@Ne (Id (Id UInt64)) (x ^^^ y) (y + 3)) (@instDecidableNot (@Eq (Id (Id UInt64)) (x ^^^ y) (y + 3)) (instDecidableEqUInt64 (x ^^^ y) (y + 3)))))
    (x + 1) (y * 3)

def reannotatedGuardHelper (x y : UInt64) : UInt64 :=
  let f := fun z : UInt64 =>
    @ite UInt64
      ((@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3)) ∨ (@Ne (Id (Id UInt64)) (z % 5) (0)))
      (@instDecidableOr (@LT.lt (Id UInt64) instLTUInt64 (z + 1) (y * 3)) (@Ne (Id (Id UInt64)) (z % 5) (0))
        (UInt64.decLt (z + 1) (y * 3)) (@instDecidableNot (@Eq (Id (Id UInt64)) (z % 5) (0)) (instDecidableEqUInt64 (z % 5) (0))))
      (z + 1) (z * 3)
  f x + f y

def reannotatedGuardDo (x y : UInt64) : UInt64 := Id.run do
  let value ← @ite (Id UInt64)
    ((@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) ∧ (@Eq (Id (Id UInt64)) ((x + y) % 5) (0)))
    (@instDecidableAnd (@LT.lt (Id UInt64) instLTUInt64 (x + 1) (y * 7)) (@Eq (Id (Id UInt64)) ((x + y) % 5) (0))
      (UInt64.decLt (x + 1) (y * 7)) (instDecidableEqUInt64 ((x + y) % 5) (0)))
    (pure (x + 1)) (pure (y * 3))
  return value + y

def rangeReannotatedAnd (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      ((@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) ∧ (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)))
      (@instDecidableAnd (@GE.ge (Id (Id UInt64)) instLEUInt64 (UInt64.ofNat i + 1) (seed % 7)) (@Ne (Id UInt64) ((a + UInt64.ofNat i) % 5) (0))
        (UInt64.decLe (seed % 7) (UInt64.ofNat i + 1)) (@instDecidableNot (@Eq (Id UInt64) ((a + UInt64.ofNat i) % 5) (0)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 5) (0))))
      (pure (.done (a + UInt64.ofNat i))) (pure (.yield (a * 3 + UInt64.ofNat i)))

def rangeReannotatedOr (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    @ite (Id (ForInStep UInt64))
      ((@GT.gt (Id UInt64) instLTUInt64 (UInt64.ofNat i + 1) (seed % 11)) ∨ (@Eq (Id (Id UInt64)) ((a + UInt64.ofNat i) % 7) (0)))
      (@instDecidableOr (@GT.gt (Id UInt64) instLTUInt64 (UInt64.ofNat i + 1) (seed % 11)) (@Eq (Id (Id UInt64)) ((a + UInt64.ofNat i) % 7) (0))
        (UInt64.decLt (seed % 11) (UInt64.ofNat i + 1)) (instDecidableEqUInt64 ((a + UInt64.ofNat i) % 7) (0)))
      (pure (.done (a + UInt64.ofNat i))) (pure (.yield (a * 3 + UInt64.ofNat i)))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end GuardDecisionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`GuardDecisionTest.reannotatedAnd, GuardDecisionTest.reannotatedAnd, false),
    (`GuardDecisionTest.reannotatedOr, GuardDecisionTest.reannotatedOr, false),
    (`GuardDecisionTest.reannotatedGuardNegation, GuardDecisionTest.reannotatedGuardNegation, false),
    (`GuardDecisionTest.reannotatedNestedGuard, GuardDecisionTest.reannotatedNestedGuard, false),
    (`GuardDecisionTest.reannotatedGuardHelper, GuardDecisionTest.reannotatedGuardHelper, false),
    (`GuardDecisionTest.reannotatedGuardDo, GuardDecisionTest.reannotatedGuardDo, false),
    (`GuardDecisionTest.rangeReannotatedAnd, GuardDecisionTest.rangeReannotatedAnd, true),
    (`GuardDecisionTest.rangeReannotatedOr, GuardDecisionTest.rangeReannotatedOr, true)]
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
      else GuardDecisionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 132 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/compound-decision IR comparisons passed"
