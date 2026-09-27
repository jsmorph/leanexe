import LeanExe.Extract.ScalarFunc

namespace BooleanPropositionLetRelationTest

def booleanPropLetRelationWord (x y : UInt64) : UInt64 :=
  if (let b := x == y; b = (x == 0)) then x + 7 else y + 11

def booleanPropLetRelationDecision (x y : UInt64) : Bool :=
  decide (let b := x == y; b ≠ (x == 0))

def booleanPropLetRelationDependent (x y : UInt64) : Bool :=
  if _h : (let b := x == y; b = (y == 0)) then x != 0 else y != 0

def booleanPropLetRelationNested (x y : UInt64) : Id (Id Bool) :=
  pure (pure (decide (let n := x + y; let b := n == x; b ≠ (y == 0))))

def booleanPropLetRelationHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && y != 0
  if (let flag := f (x == y); flag = f (x == 0)) then x - 3 else y * 7

def booleanPropLetRelationUnused (x y : UInt64) : UInt64 :=
  if (let _unused := x + y; (x == 0) ≠ (y == 0)) then x + y else x - y

def rangeBoolLetRelationStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let b := a % 2 == 0; b = (i.toUInt64 % 3 == 0)) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeBoolLetRelationExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let b := a % 7 == 0; b ≠ (i.toUInt64 % 3 == 0)) then break
  return a

def rangeBoolLetRelationContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ (let b := a % 2 == 0; b = (i.toUInt64 % 3 == 0)) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBoolLetRelationTail (count seed : UInt64) : Id Bool := do
  let value ← (do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
    return a)
  return decide (let b := value == seed; b = (seed == 0))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPropositionLetRelationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPropositionLetRelationTest.booleanPropLetRelationWord, (fun (x y : UInt64) => BooleanPropositionLetRelationTest.booleanPropLetRelationWord x y), false),
    (`BooleanPropositionLetRelationTest.booleanPropLetRelationDecision, (fun (x y : UInt64) => (BooleanPropositionLetRelationTest.booleanPropLetRelationDecision x y).toUInt64), false),
    (`BooleanPropositionLetRelationTest.booleanPropLetRelationDependent, (fun (x y : UInt64) => (BooleanPropositionLetRelationTest.booleanPropLetRelationDependent x y).toUInt64), false),
    (`BooleanPropositionLetRelationTest.booleanPropLetRelationNested, (fun (x y : UInt64) => (BooleanPropositionLetRelationTest.booleanPropLetRelationNested x y).toUInt64), false),
    (`BooleanPropositionLetRelationTest.booleanPropLetRelationHelper, (fun (x y : UInt64) => BooleanPropositionLetRelationTest.booleanPropLetRelationHelper x y), false),
    (`BooleanPropositionLetRelationTest.booleanPropLetRelationUnused, (fun (x y : UInt64) => BooleanPropositionLetRelationTest.booleanPropLetRelationUnused x y), false),
    (`BooleanPropositionLetRelationTest.rangeBoolLetRelationStep, (fun (x y : UInt64) => BooleanPropositionLetRelationTest.rangeBoolLetRelationStep x y), true),
    (`BooleanPropositionLetRelationTest.rangeBoolLetRelationExit, (fun (x y : UInt64) => BooleanPropositionLetRelationTest.rangeBoolLetRelationExit x y), true),
    (`BooleanPropositionLetRelationTest.rangeBoolLetRelationContinue, (fun (x y : UInt64) => BooleanPropositionLetRelationTest.rangeBoolLetRelationContinue x y), true),
    (`BooleanPropositionLetRelationTest.rangeBoolLetRelationTail, (fun (x y : UInt64) => (BooleanPropositionLetRelationTest.rangeBoolLetRelationTail x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean proposition-let relation extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanPropositionLetRelationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean proposition-let relation IR comparisons passed"
