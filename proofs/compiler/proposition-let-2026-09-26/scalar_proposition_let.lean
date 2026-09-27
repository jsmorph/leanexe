import LeanExe.Extract.ScalarFunc

namespace PropositionLetTest

def propositionLetNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if (let flag := f (x == 0); let word := x + flag.toUInt64; f (word != y)) ∧ x < y then x + y else x - y

def propositionLetWord (x y : UInt64) : UInt64 :=
  if (let word := x + y; word < x ∨ word = y) then x + 1 else y + 2

def propositionLetDecision (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let flag := decide ((let saved := f (x != 0); !saved) ∨ (let word := x + 1; word ≤ y))
  flag.toUInt64 + x

def propositionLetDependent (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if _h : (let saved := f (x == 0); saved) ∧ x < y then x + 3 else y + 7

def propositionLetUnused (x y : UInt64) : UInt64 :=
  if (let _saved := x == y; let _word := x + y; True) then y + 1 else x

def propositionLetHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let g := fun b : Bool => if (let saved := f b; !saved) ∧ x < y then f true else f false
  (g true).toUInt64 + (g false).toUInt64 + y

def rangePropositionLetStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != 0
    if (let saved := f (i.toUInt64 != seed); saved || f true) ∧ i.toUInt64 < a then break
    a := a + i.toUInt64 + 1
  return a

def rangePropositionLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n != seed
    if a = 0 ∨ (let flag := f i.toUInt64; !flag) then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangePropositionLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let mut a := if (let saved := f true; saved) ∧ count < seed then seed + 1 else seed
  for i in [:count.toNat] do
    if (let word := a + i.toUInt64; word < seed) then a := a + 2 else a := a + 1
  return a + (decide ((let saved := f true; saved) ∨ a = seed)).toUInt64

def rangePropositionLetHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if (let flag := f b; !flag) ∧ seed < count then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if (let flag := g (a == 0); flag) ∧ i.toUInt64 < a then break
    a := a + (f (g true)).toUInt64 + 1
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PropositionLetTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PropositionLetTest.propositionLetNested, PropositionLetTest.propositionLetNested, false),
    (`PropositionLetTest.propositionLetWord, PropositionLetTest.propositionLetWord, false),
    (`PropositionLetTest.propositionLetDecision, PropositionLetTest.propositionLetDecision, false),
    (`PropositionLetTest.propositionLetDependent, PropositionLetTest.propositionLetDependent, false),
    (`PropositionLetTest.propositionLetUnused, PropositionLetTest.propositionLetUnused, false),
    (`PropositionLetTest.propositionLetHelper, PropositionLetTest.propositionLetHelper, false),
    (`PropositionLetTest.rangePropositionLetStep, PropositionLetTest.rangePropositionLetStep, true),
    (`PropositionLetTest.rangePropositionLetContinue, PropositionLetTest.rangePropositionLetContinue, true),
    (`PropositionLetTest.rangePropositionLetOuter, PropositionLetTest.rangePropositionLetOuter, true),
    (`PropositionLetTest.rangePropositionLetHelper, PropositionLetTest.rangePropositionLetHelper, true)]
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
      else PropositionLetTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/proposition-let IR comparisons passed"
