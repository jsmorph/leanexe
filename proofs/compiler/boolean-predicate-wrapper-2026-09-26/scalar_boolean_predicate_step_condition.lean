import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateStepConditionTest

def rangeBooleanPredicateConditionBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun flag : Bool => flag || a % 7 == 0
    if f (UInt64.ofNat i == seed % 9) then break
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateConditionSkip (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun flag : Bool => !flag || a == seed
    if !f (UInt64.ofNat i % 3 == 0) then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateConditionEq (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun b : Bool => b != (a % 5 == 0)
    if f (UInt64.ofNat i == seed % 11) = false then .done (a + 7)
    else .yield (a + UInt64.ofNat i + 1)

def rangeBooleanPredicateConditionNe (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun b : Bool => b && a != 0
    if f (UInt64.ofNat i % 3 == 0) ≠ f (seed == 0) then .yield (a + 11)
    else .done (a + UInt64.ofNat i)

def rangeBooleanPredicateConditionProof (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f := fun b : Bool => !b || a % 7 == 0
    if _h : f (UInt64.ofNat i != seed % 13) then pure (.done (a + 3))
    else pure (.yield (a + UInt64.ofNat i + 1))

def rangeBooleanPredicateConditionOuterBreak (count seed : UInt64) : UInt64 := Id.run do
  let captured := seed == 0
  let f := fun b : Bool => b || captured
  let mut a := seed
  for i in [:count.toNat] do
    if f (UInt64.ofNat i == seed % 11) then break
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateConditionNestedStep (count seed : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let g := fun b : Bool => b || a == seed
    if f (g (UInt64.ofNat i % 3 == 0)) then pure (.done (a + 7))
    else if _h : g (UInt64.ofNat i == seed % 7) ≠ false then pure (.yield (a + 2))
    else pure (.done a)

def rangeBooleanPredicateConditionIdStep (count seed : UInt64) : UInt64 :=
  let f : Bool → Id (Id Bool) := fun b => !b
  forIn (m := Id) [:count.toNat] seed fun i a =>
    if _h : @Eq Bool (f (UInt64.ofNat i % 3 == 0)) false then .yield (a + 3)
    else .done (a + UInt64.ofNat i)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateStepConditionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionBreak, BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionBreak, true),
    (`BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionSkip, BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionSkip, true),
    (`BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionEq, BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionEq, true),
    (`BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionNe, BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionNe, true),
    (`BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionProof, BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionProof, true),
    (`BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionOuterBreak, BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionOuterBreak, true),
    (`BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionNestedStep, BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionNestedStep, true),
    (`BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionIdStep, BooleanPredicateStepConditionTest.rangeBooleanPredicateConditionIdStep, true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reusable Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanPredicateStepConditionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate step condition IR comparisons passed"
