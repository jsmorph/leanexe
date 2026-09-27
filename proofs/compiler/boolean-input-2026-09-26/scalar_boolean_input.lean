import LeanExe.Extract.ScalarFunc

namespace BooleanInputTest

def booleanInputWord (x y : UInt64) : UInt64 :=
  let f : Id Bool → UInt64 := fun (b : Id Bool) => if Id.run b then x + y else x - y
  f (x == 0) + f (x != y)

def booleanInputPredicate (x y : UInt64) : UInt64 :=
  let f : Id Bool → Id Bool := fun (b : Id Bool) => b || x == y
  (f (x == 0)).toUInt64 + (f (x != y)).toUInt64 + x

def booleanInputNested (x y : UInt64) : UInt64 :=
  let f : Id (Id Bool) → Id (Id Bool) := fun (b : Id (Id Bool)) => b && x != y
  let g : Id Bool → Id UInt64 := fun (b : Id Bool) => (f b).toUInt64 + y
  Id.run (g (x == 0)) + Id.run (g (x != y))

def booleanInputUnused (x y : UInt64) : UInt64 :=
  let _unused : Id Bool → UInt64 := fun (b : Id Bool) => if Id.run b then x / 0 else y % 0
  x + y

def booleanInputDecision (x y : UInt64) : UInt64 :=
  let f : Id Bool → Bool := fun (b : Id Bool) => b || x == y
  let g : Id (Id Bool) → Bool := fun (b : Id (Id Bool)) => if ¬ f b then !b else b
  (decide (g true ∧ x < y)).toUInt64 + (g false).toUInt64 + y

def booleanInputBind (x y : UInt64) : UInt64 := Id.run do
  let f : Id Bool → Id (Id UInt64) := fun (b : Id Bool) => do
    let saved ← pure (b || x == y)
    return (show UInt64 from if saved then x + 3 else y + 7)
  let a ← f (x == 0)
  return Id.run a + Id.run (← f (decide (Id.run a < y)))

def rangeBooleanInputStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Id Bool → Id (ForInStep UInt64) := fun (flag : Id Bool) => do
      let g : Id (Id Bool) → ForInStep UInt64 := fun (inner : Id (Id Bool)) =>
        if flag && !inner then .done (a + i.toUInt64) else .yield (a - count)
      return g (a == seed)
    f (i.toUInt64 % 3 == 0)

def rangeBooleanInputContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Id Bool → Id Bool := fun (b : Id Bool) => b && a != 0
    if Id.run (f (i.toUInt64 == seed)) then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeBooleanInputOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := seed != 0
  let f : Id (Id Bool) → UInt64 := fun (b : Id (Id Bool)) => if b || flag then seed + 1 else seed
  let mut a := f (count == 0)
  for i in [:count.toNat] do
    if a < f (i.toUInt64 == 0) then break
    a := a + i.toUInt64 + 1
  return a + f (a == seed)

def rangeBooleanInputHelper (count seed : UInt64) : UInt64 := Id.run do
  let f : Id Bool → Id Bool := fun (b : Id Bool) => b && seed != 0
  let mut a := seed
  for i in [:count.toNat] do
    let g : Id (Id Bool) → UInt64 := fun (b : Id (Id Bool)) => (f b).toUInt64 + a
    if g (i.toUInt64 == 0) < seed then break
    a := g (a == seed) + i.toUInt64 + 1
  return a + (f (a == seed)).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanInputTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanInputTest.booleanInputWord, BooleanInputTest.booleanInputWord, false),
    (`BooleanInputTest.booleanInputPredicate, BooleanInputTest.booleanInputPredicate, false),
    (`BooleanInputTest.booleanInputNested, BooleanInputTest.booleanInputNested, false),
    (`BooleanInputTest.booleanInputUnused, BooleanInputTest.booleanInputUnused, false),
    (`BooleanInputTest.booleanInputDecision, BooleanInputTest.booleanInputDecision, false),
    (`BooleanInputTest.booleanInputBind, BooleanInputTest.booleanInputBind, false),
    (`BooleanInputTest.rangeBooleanInputStep, BooleanInputTest.rangeBooleanInputStep, true),
    (`BooleanInputTest.rangeBooleanInputContinue, BooleanInputTest.rangeBooleanInputContinue, true),
    (`BooleanInputTest.rangeBooleanInputOuter, BooleanInputTest.rangeBooleanInputOuter, true),
    (`BooleanInputTest.rangeBooleanInputHelper, BooleanInputTest.rangeBooleanInputHelper, true)]
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
      else BooleanInputTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/boolean-input IR comparisons passed"
