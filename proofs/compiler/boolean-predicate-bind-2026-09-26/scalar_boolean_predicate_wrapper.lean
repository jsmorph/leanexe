import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateWrapperTest

def booleanPredicateWrapper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b && x != 0
  (Id.run (pure (f (x == y)))).toUInt64

def booleanPredicateWrapperNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  (!(Id.run (pure (Id.run (pure (f true)))))).toUInt64 +
    (Id.run (pure (!(f false)))).toUInt64

def booleanPredicateWrapperLet (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let flag := Id.run (pure (f (x != 0)))
  let saved := flag
  let flag := Id.run (pure (f (!saved)))
  if saved then x + flag.toUInt64 else y + flag.toUInt64

def booleanPredicateWrapperCondition (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  if _h : Id.run (pure (f (x == y))) = false then x + 7 else y + 11

def booleanPredicateWrapperArgument (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == y
  (f (Id.run (pure (f (x == 0))))).toUInt64 +
    (Id.run (pure (f (Id.run (pure (f false)))))).toUInt64

def booleanPredicateWrapperBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == 0
  let g := fun b : Bool => (Id.run (pure (f b))).toUInt64 == 0 && y != 0
  (Id.run (pure (g (x == y)))).toUInt64

def rangeBooleanPredicateWrapperStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    if Id.run (pure (f (UInt64.ofNat i == seed % 7))) then break
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateWrapperContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => !b || a == seed
    if !(Id.run (pure (f (UInt64.ofNat i % 3 == 0)))) then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateWrapperOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let flag := Id.run (pure (f (count == 0)))
  let stop := count + (Id.run (pure (f false))).toUInt64
  let mut a := seed + flag.toUInt64
  for i in [:stop.toNat] do
    a := a + UInt64.ofNat i + 1
    if _h : Id.run (pure (f (a % 7 == 0))) ≠ false then break
  return a + (Id.run (pure (f (a == seed)))).toUInt64

def rangeBooleanPredicateWrapperCapture (count seed : UInt64) : UInt64 :=
  let f := fun b : Bool => b && seed != 0
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let g := fun b : Bool => (Id.run (pure (f b))).toUInt64 == 0
    let flag := Id.run (pure (g (UInt64.ofNat i % 3 == 0)))
    if flag then .yield (a + 3) else .done (a + UInt64.ofNat i)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateWrapperTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateWrapperTest.booleanPredicateWrapper, BooleanPredicateWrapperTest.booleanPredicateWrapper, false),
    (`BooleanPredicateWrapperTest.booleanPredicateWrapperNested, BooleanPredicateWrapperTest.booleanPredicateWrapperNested, false),
    (`BooleanPredicateWrapperTest.booleanPredicateWrapperLet, BooleanPredicateWrapperTest.booleanPredicateWrapperLet, false),
    (`BooleanPredicateWrapperTest.booleanPredicateWrapperCondition, BooleanPredicateWrapperTest.booleanPredicateWrapperCondition, false),
    (`BooleanPredicateWrapperTest.booleanPredicateWrapperArgument, BooleanPredicateWrapperTest.booleanPredicateWrapperArgument, false),
    (`BooleanPredicateWrapperTest.booleanPredicateWrapperBody, BooleanPredicateWrapperTest.booleanPredicateWrapperBody, false),
    (`BooleanPredicateWrapperTest.rangeBooleanPredicateWrapperStep, BooleanPredicateWrapperTest.rangeBooleanPredicateWrapperStep, true),
    (`BooleanPredicateWrapperTest.rangeBooleanPredicateWrapperContinue, BooleanPredicateWrapperTest.rangeBooleanPredicateWrapperContinue, true),
    (`BooleanPredicateWrapperTest.rangeBooleanPredicateWrapperOuter, BooleanPredicateWrapperTest.rangeBooleanPredicateWrapperOuter, true),
    (`BooleanPredicateWrapperTest.rangeBooleanPredicateWrapperCapture, BooleanPredicateWrapperTest.rangeBooleanPredicateWrapperCapture, true)]
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
      else BooleanPredicateWrapperTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate wrapper IR comparisons passed"
