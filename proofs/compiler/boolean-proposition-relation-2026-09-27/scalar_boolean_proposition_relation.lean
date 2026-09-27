import LeanExe.Extract.ScalarFunc

namespace BooleanPropositionRelationTest

def booleanPropRelationDecision (left right : Bool) : Id (Id Bool) :=
  pure (pure (decide (left = right ∨ ¬ left)))

def booleanPropRelationMixed (left right : Bool) : UInt64 :=
  if left ≠ right ∧ left then 7 else 11

def booleanPropRelationNegated (left right : Bool) : Bool :=
  decide (¬ (left = right) ∧ ¬ (left ≠ right ∧ right))

def booleanPropRelationWords (x y : UInt64) : UInt64 :=
  let left := x == y
  let right := x != 0
  if (left ≠ right ∨ x < y) ∧ (right = left ∨ y < x) then x + 7 else y - 3

def booleanPropRelationHelpers (x y : UInt64) : Id Bool := do
  let f := fun b : Bool => b && x != 0
  let g := fun n : UInt64 => n == y
  return decide (f (x == y) = g x ∧ (g y ≠ f false ∨ x < y))

def booleanPropRelationLet (x y : UInt64) : UInt64 :=
  if (let flag := x == y; flag ≠ (x == 0) ∧ x < y) then x + 3 else y + 7

def rangeBoolRelationStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := i.toUInt64 % 3 == 0
    if first = second ∨ ¬ first then a := a + i.toUInt64 + 7 else a := a * 3 + 1
  return a

def rangeBoolRelationExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (a % 2 == 0) ≠ (i.toUInt64 % 3 == 0) ∧ a > 7 then break
  return a

def rangeBoolRelationContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ ((a % 2 == 0) = (i.toUInt64 % 3 == 0)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBoolRelationTail (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a)
  return decide ((value == seed) = (seed == 0) ∨ ¬ (value == 0))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPropositionRelationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPropositionRelationTest.booleanPropRelationDecision, (fun (x y : UInt64) => (BooleanPropositionRelationTest.booleanPropRelationDecision (x != 0) (y != 0)).toUInt64), false),
    (`BooleanPropositionRelationTest.booleanPropRelationMixed, (fun (x y : UInt64) => BooleanPropositionRelationTest.booleanPropRelationMixed (x != 0) (y != 0)), false),
    (`BooleanPropositionRelationTest.booleanPropRelationNegated, (fun (x y : UInt64) => (BooleanPropositionRelationTest.booleanPropRelationNegated (x != 0) (y != 0)).toUInt64), false),
    (`BooleanPropositionRelationTest.booleanPropRelationWords, (fun (x y : UInt64) => BooleanPropositionRelationTest.booleanPropRelationWords x y), false),
    (`BooleanPropositionRelationTest.booleanPropRelationHelpers, (fun (x y : UInt64) => (BooleanPropositionRelationTest.booleanPropRelationHelpers x y).toUInt64), false),
    (`BooleanPropositionRelationTest.booleanPropRelationLet, (fun (x y : UInt64) => BooleanPropositionRelationTest.booleanPropRelationLet x y), false),
    (`BooleanPropositionRelationTest.rangeBoolRelationStep, (fun (x y : UInt64) => BooleanPropositionRelationTest.rangeBoolRelationStep x y), true),
    (`BooleanPropositionRelationTest.rangeBoolRelationExit, (fun (x y : UInt64) => BooleanPropositionRelationTest.rangeBoolRelationExit x y), true),
    (`BooleanPropositionRelationTest.rangeBoolRelationContinue, (fun (x y : UInt64) => BooleanPropositionRelationTest.rangeBoolRelationContinue x y), true),
    (`BooleanPropositionRelationTest.rangeBoolRelationTail, (fun (x y : UInt64) => (BooleanPropositionRelationTest.rangeBoolRelationTail x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean proposition relation extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanPropositionRelationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean proposition relation IR comparisons passed"
