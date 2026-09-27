import LeanExe.Extract.ScalarFunc

namespace PropositionHelperLetTest

def propositionHelperLetCompound (x y : UInt64) : UInt64 :=
  (if x < y ∧ (let f := fun n : UInt64 => n == y; f x || f 0) then
    (let g := fun b : Bool => b || y == 0; g (x == 0)) else x == y).toUInt64 + x

def propositionHelperLetBoolean (x y : UInt64) : UInt64 :=
  if (let f := fun b : Bool => b || x == y; f (x == 0) && f (y == 0)) ∨ x < y then
    x + 7 else y * 3

def propositionHelperLetDecision (x y : UInt64) : UInt64 :=
  (decide (¬ (let f := fun n : UInt64 => n % 3 == 0; f x = f y) ∧ x ≤ y)).toUInt64 + y

def propositionHelperLetDependent (x y : UInt64) : UInt64 :=
  (if _h : (let f := fun b : Bool => b && x != y; f (x == 0) ≠ f (y == 0)) ∨ y < x then
    (let g := fun n : UInt64 => n == x; g y || g 0)
   else !(x == y)).toUInt64 + x

def propositionHelperLetUnused (x y : UInt64) : UInt64 :=
  if (let _unused := fun n : UInt64 => n == y; True) ∧
      (let _unused := fun b : Bool => b || x == y; True) then x + y else 0

def propositionHelperLetNested (x y : UInt64) : UInt64 :=
  if (let f := fun n : UInt64 => n == y; let word := x + y;
      let flag := f word; flag = f x) then x + 1 else y + 2

def rangePropositionHelperLetStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => n % 3 == 0; f a || f i.toUInt64) ∧ a ≤ seed then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangePropositionHelperLetExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (let f := fun b : Bool => b || seed == 0; f (a % 7 == 0) ≠ f (i.toUInt64 == 0)) ∨ a = seed then break
  return a

def rangePropositionHelperLetContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => n % 3 == 0; let flag := f a; flag = f i.toUInt64) ∧ seed ≤ a then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangePropositionHelperLetTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (decide ((let f := fun b : Bool => !b || seed == 0; f (a == seed) && f (a == 0)) ∨ a < seed)).toUInt64 + a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PropositionHelperLetTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PropositionHelperLetTest.propositionHelperLetCompound, (fun (x y : UInt64) => PropositionHelperLetTest.propositionHelperLetCompound x y), false),
    (`PropositionHelperLetTest.propositionHelperLetBoolean, (fun (x y : UInt64) => PropositionHelperLetTest.propositionHelperLetBoolean x y), false),
    (`PropositionHelperLetTest.propositionHelperLetDecision, (fun (x y : UInt64) => PropositionHelperLetTest.propositionHelperLetDecision x y), false),
    (`PropositionHelperLetTest.propositionHelperLetDependent, (fun (x y : UInt64) => PropositionHelperLetTest.propositionHelperLetDependent x y), false),
    (`PropositionHelperLetTest.propositionHelperLetUnused, (fun (x y : UInt64) => PropositionHelperLetTest.propositionHelperLetUnused x y), false),
    (`PropositionHelperLetTest.propositionHelperLetNested, (fun (x y : UInt64) => PropositionHelperLetTest.propositionHelperLetNested x y), false),
    (`PropositionHelperLetTest.rangePropositionHelperLetStep, (fun (x y : UInt64) => PropositionHelperLetTest.rangePropositionHelperLetStep x y), true),
    (`PropositionHelperLetTest.rangePropositionHelperLetExit, (fun (x y : UInt64) => PropositionHelperLetTest.rangePropositionHelperLetExit x y), true),
    (`PropositionHelperLetTest.rangePropositionHelperLetContinue, (fun (x y : UInt64) => PropositionHelperLetTest.rangePropositionHelperLetContinue x y), true),
    (`PropositionHelperLetTest.rangePropositionHelperLetTail, (fun (x y : UInt64) => PropositionHelperLetTest.rangePropositionHelperLetTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: proposition predicate-let extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PropositionHelperLetTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/proposition predicate-let IR comparisons passed"
