import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateLoopResultTest

def rangeBooleanPredicateResultLocalBool (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    let g := fun b : Bool => !(f b)
    if g ((UInt64.ofNat i) < seed) then
      a := a + 7
      break
    a := a + (UInt64.ofNat i) + 1
  return a

def rangeBooleanPredicateResultLocalWord (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == seed
    let g := fun n : UInt64 => f (n == (UInt64.ofNat i))
    if g a then
      a := a + 3
      continue
    a := a + (UInt64.ofNat i) + 1
  return a

def rangeBooleanPredicateResultLocalNested (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    let g := fun b : Bool => f (!b)
    let h := fun n : UInt64 => g (n == (UInt64.ofNat i))
    if h seed then break
    a := a + (g (h a)).toUInt64 + 1
  return a

def rangeBooleanPredicateResultLocalWrapped (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    let g : Bool → Id (Id Bool) := fun b => pure (Id.run (pure (f b)))
    let h : Id (Id UInt64) → Id Bool := fun n => pure (g ((show UInt64 from n) == (UInt64.ofNat i)))
    if Id.run (h a) then
      a := a + 9
      break
    a := a + (g true).toUInt64 + 1
  return a

def rangeBooleanPredicateResultOuterBool (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => !(f b)
  let mut a := seed + (g true).toUInt64
  for i in [:count.toNat] do
    if g (a == (UInt64.ofNat i)) then
      a := a + 5
      continue
    a := a + 1
  return a + (g false).toUInt64

def rangeBooleanPredicateResultOuterWord (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun n : UInt64 => f (n == seed)
  let mut a := seed
  for i in [:(count + (g 0).toUInt64).toNat] do
    if g (a + (UInt64.ofNat i)) then break
    a := a + 1
  return a + (g seed).toUInt64

def rangeBooleanPredicateResultOuterNested (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => f (!b)
  let h := fun n : UInt64 => g (n == seed)
  let mut a := seed
  for i in [:count.toNat] do
    let localHelper := fun b : Bool => h (a + b.toUInt64)
    if localHelper ((UInt64.ofNat i) == seed) then break
    a := a + (g (h a)).toUInt64 + 1
  return a + (h seed).toUInt64

def rangeBooleanPredicateResultOuterWrapped (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g : Bool → Id (Id Bool) := fun b => pure (Id.run (pure (f b)))
  let h : Id (Id UInt64) → Id Bool := fun n => pure (g ((show UInt64 from n) == seed))
  let unused := fun b : Bool => g (!b)
  let mut a := seed + (g true).toUInt64
  for i in [:count.toNat] do
    if Id.run (h (a + (UInt64.ofNat i))) then break
    a := a + 1
  return a + (g false).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateLoopResultTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateLoopResultTest.rangeBooleanPredicateResultLocalBool, BooleanPredicateLoopResultTest.rangeBooleanPredicateResultLocalBool, true),
    (`BooleanPredicateLoopResultTest.rangeBooleanPredicateResultLocalWord, BooleanPredicateLoopResultTest.rangeBooleanPredicateResultLocalWord, true),
    (`BooleanPredicateLoopResultTest.rangeBooleanPredicateResultLocalNested, BooleanPredicateLoopResultTest.rangeBooleanPredicateResultLocalNested, true),
    (`BooleanPredicateLoopResultTest.rangeBooleanPredicateResultLocalWrapped, BooleanPredicateLoopResultTest.rangeBooleanPredicateResultLocalWrapped, true),
    (`BooleanPredicateLoopResultTest.rangeBooleanPredicateResultOuterBool, BooleanPredicateLoopResultTest.rangeBooleanPredicateResultOuterBool, true),
    (`BooleanPredicateLoopResultTest.rangeBooleanPredicateResultOuterWord, BooleanPredicateLoopResultTest.rangeBooleanPredicateResultOuterWord, true),
    (`BooleanPredicateLoopResultTest.rangeBooleanPredicateResultOuterNested, BooleanPredicateLoopResultTest.rangeBooleanPredicateResultOuterNested, true),
    (`BooleanPredicateLoopResultTest.rangeBooleanPredicateResultOuterWrapped, BooleanPredicateLoopResultTest.rangeBooleanPredicateResultOuterWrapped, true)]
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
      else BooleanPredicateLoopResultTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate loop result IR comparisons passed"
