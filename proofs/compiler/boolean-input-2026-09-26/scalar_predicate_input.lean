import LeanExe.Extract.ScalarFunc

namespace PredicateInputTest

def predicateInputRepeated (x y : UInt64) : UInt64 :=
  let f : Id UInt64 → Bool := fun n => (show UInt64 from n) == y
  if f x || f (x + 1) then x + 7 else y - 3

def predicateInputNested (x y : UInt64) : UInt64 :=
  let f : Id (Id UInt64) → Id (Id Bool) := fun n => (show UInt64 from n) == y
  let g : Id UInt64 → Bool := fun n => !(f (show UInt64 from n)) && f ((show UInt64 from n) + 1)
  (g x).toUInt64 + (g y).toUInt64 * 3

def predicateInputCapture (x y : UInt64) : UInt64 :=
  let flag := x != 0
  let shift := fun n : UInt64 => n + y
  let f : Id (Id (Id UInt64)) → Bool := fun n => flag && shift (show UInt64 from n) != x
  (f x).toUInt64 + (f y).toUInt64 * 7

def predicateInputShadow (x y : UInt64) : UInt64 :=
  let f : Id UInt64 → Bool := fun n => (show UInt64 from n) == x
  let saved := f y
  let f : Id (Id UInt64) → Bool := fun n => saved || (show UInt64 from n) != y
  if f x && f y then x - y else x + y

def predicateInputUnused (x y : UInt64) : UInt64 :=
  let _f : Id (Id UInt64) → Id Bool := fun n => (show UInt64 from n) / y == x
  x - y

def predicateInputDo (x y : UInt64) : UInt64 := Id.run do
  let f : Id UInt64 → Bool := fun n => (show UInt64 from n) != y
  let a ← pure (f x)
  let b ← pure (f (x + 1))
  if a && b then return x + y else return x - y

def rangePredicateInputStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Id UInt64 → Bool := fun n => (show UInt64 from n) % 7 == 0
    a := a + UInt64.ofNat i
    if f a || f (a + 1) then break
  return a

def rangePredicateInputStepCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Id (Id UInt64) → Id Bool := fun n => (show UInt64 from n) == a
    let g : Id UInt64 → Bool := fun n => !(f (show UInt64 from n)) && f ((show UInt64 from n) + 1)
    if g (UInt64.ofNat i) then continue
    a := a + (g a).toUInt64 + UInt64.ofNat i
  return a

def rangePredicateInputOuter (count seed : UInt64) : UInt64 := Id.run do
  let f : Id (Id UInt64) → Bool := fun n => (show UInt64 from n) % 5 == 0
  let first := (f seed).toUInt64
  let mut a := seed
  for i in [first.toNat:count.toNat:3] do
    a := a + UInt64.ofNat i
    if f a || f (a + 1) then break
  return a + (f a).toUInt64

def rangePredicateInputOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let f : Id UInt64 → Id (Id Bool) := fun n => flag && (show UInt64 from n) == seed
  let g := fun n : UInt64 => if (show Bool from f n) then n + 1 else n * 3
  let mut a := seed
  for i in [:count.toNat] do
    a := g (a + UInt64.ofNat i)
    if (show Bool from f a) then break
  return g a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PredicateInputTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PredicateInputTest.predicateInputRepeated, PredicateInputTest.predicateInputRepeated, false),
    (`PredicateInputTest.predicateInputNested, PredicateInputTest.predicateInputNested, false),
    (`PredicateInputTest.predicateInputCapture, PredicateInputTest.predicateInputCapture, false),
    (`PredicateInputTest.predicateInputShadow, PredicateInputTest.predicateInputShadow, false),
    (`PredicateInputTest.predicateInputUnused, PredicateInputTest.predicateInputUnused, false),
    (`PredicateInputTest.predicateInputDo, PredicateInputTest.predicateInputDo, false),
    (`PredicateInputTest.rangePredicateInputStep, PredicateInputTest.rangePredicateInputStep, true),
    (`PredicateInputTest.rangePredicateInputStepCapture, PredicateInputTest.rangePredicateInputStepCapture, true),
    (`PredicateInputTest.rangePredicateInputOuter, PredicateInputTest.rangePredicateInputOuter, true),
    (`PredicateInputTest.rangePredicateInputOuterCapture, PredicateInputTest.rangePredicateInputOuterCapture, true)]
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
      else PredicateInputTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/predicate-input IR comparisons passed"
