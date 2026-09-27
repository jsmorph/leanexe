import LeanExe.Extract.ScalarFunc

namespace DecisionLetTest

def decisionLetUnused (x y : UInt64) : UInt64 :=
  if (let _saved := x == y; True) ∧ (let _word := x + y; False) then x else y + 1

def decisionLetLeft (x y : UInt64) : UInt64 :=
  if (let _word := x + y; let _saved := x == y; True) ∧ x < y then x + 3 else y + 7

def decisionLetRight (x y : UInt64) : UInt64 :=
  let flag := x == 0
  if flag ∨ (let _word := x + y; False) then x + 1 else y + 2

def decisionLetDependent (x y : UInt64) : UInt64 :=
  let flag := x == y
  if _h : (let _saved := flag; True) ∧ flag then x + y else x - y

def decisionLetSaved (x y : UInt64) : UInt64 :=
  let flag := decide ((let _saved := x == 0; False) ∨ (let _word := x + y; True))
  flag.toUInt64 + x

def decisionLetHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => if (let _saved := b; True) ∧ x < y then !b else b
  (f true).toUInt64 + (f false).toUInt64 + y

def rangeDecisionLetStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let _saved := a == seed; True) ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangeDecisionLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if a = seed ∨ (let _word := a + i.toUInt64; False) then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeDecisionLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let mut a := if flag ∧ (let _saved := flag; True) then seed + 1 else seed
  for i in [:count.toNat] do
    if (let _word := a + i.toUInt64; False) ∨ a < seed then a := a + 2 else a := a + 1
  return a + (decide ((let _saved := flag; True) ∧ a = seed)).toUInt64

def rangeDecisionLetHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => if (let _saved := b; True) ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if f true ∧ (let _word := a + i.toUInt64; True) then break
    a := a + (f (a == 0)).toUInt64 + 1
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end DecisionLetTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`DecisionLetTest.decisionLetUnused, DecisionLetTest.decisionLetUnused, false),
    (`DecisionLetTest.decisionLetLeft, DecisionLetTest.decisionLetLeft, false),
    (`DecisionLetTest.decisionLetRight, DecisionLetTest.decisionLetRight, false),
    (`DecisionLetTest.decisionLetDependent, DecisionLetTest.decisionLetDependent, false),
    (`DecisionLetTest.decisionLetSaved, DecisionLetTest.decisionLetSaved, false),
    (`DecisionLetTest.decisionLetHelper, DecisionLetTest.decisionLetHelper, false),
    (`DecisionLetTest.rangeDecisionLetStep, DecisionLetTest.rangeDecisionLetStep, true),
    (`DecisionLetTest.rangeDecisionLetContinue, DecisionLetTest.rangeDecisionLetContinue, true),
    (`DecisionLetTest.rangeDecisionLetOuter, DecisionLetTest.rangeDecisionLetOuter, true),
    (`DecisionLetTest.rangeDecisionLetHelper, DecisionLetTest.rangeDecisionLetHelper, true)]
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
      else DecisionLetTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/decision-let IR comparisons passed"
