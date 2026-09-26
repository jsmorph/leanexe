import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateNestedTest

def booleanPredicateCompose (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  (f (g (x == y))).toUInt64 + (g (f false)).toUInt64 * 3

def booleanPredicateComposeRepeat (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == y
  (f (f (f (x != 0)))).toUInt64 + (f (f false)).toUInt64 * 3

def booleanPredicateComposeNot (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && y != 0
  let g := fun b : Bool => b || x == 0
  (!(f (!(g (x / y == 0))))).toUInt64 + (g (!(!(f true)))).toUInt64

def booleanPredicateComposeCapture (x y : UInt64) : UInt64 :=
  let saved := x != 0
  let f := fun b : Bool => saved || b
  let y := y + 1
  let g := fun b : Bool => b && x == y
  (f (g (x == y))).toUInt64 + (g (f false)).toUInt64 * 3

def booleanPredicateComposeBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  let g := fun b : Bool => (!(f (f b))).toUInt64 == x
  (g (f (x == y))).toUInt64 + (!(g (f false))).toUInt64

def booleanPredicateComposeId (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => b && x != y
  let g := fun b : Bool => !b || x == 0
  let a ← pure (f (g true)).toUInt64
  let b ← pure (!(g (f false))).toUInt64
  return a + b

def rangeBooleanPredicateComposeStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => !b && a != seed
    a := a + UInt64.ofNat i
    if (f (g (a % 7 == 0))).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateComposeContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (!(f (!(f (UInt64.ofNat i % 3 == 0))))).toUInt64 == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateComposeOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let stop := count + (f (g false)).toUInt64
  let mut a := seed + (g (f true)).toUInt64
  for i in [:stop.toNat] do
    if (!(f (g (a % 7 == 0)))).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (g (f (a == seed))).toUInt64

def rangeBooleanPredicateComposeOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (!(f (f b))).toUInt64 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (g (f b)).toUInt64 == 1 && a != seed
    if (h (g (a % 5 == 0))).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(g (f (a == seed)))).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateNestedTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateNestedTest.booleanPredicateCompose, BooleanPredicateNestedTest.booleanPredicateCompose, false),
    (`BooleanPredicateNestedTest.booleanPredicateComposeRepeat, BooleanPredicateNestedTest.booleanPredicateComposeRepeat, false),
    (`BooleanPredicateNestedTest.booleanPredicateComposeNot, BooleanPredicateNestedTest.booleanPredicateComposeNot, false),
    (`BooleanPredicateNestedTest.booleanPredicateComposeCapture, BooleanPredicateNestedTest.booleanPredicateComposeCapture, false),
    (`BooleanPredicateNestedTest.booleanPredicateComposeBody, BooleanPredicateNestedTest.booleanPredicateComposeBody, false),
    (`BooleanPredicateNestedTest.booleanPredicateComposeId, BooleanPredicateNestedTest.booleanPredicateComposeId, false),
    (`BooleanPredicateNestedTest.rangeBooleanPredicateComposeStep, BooleanPredicateNestedTest.rangeBooleanPredicateComposeStep, true),
    (`BooleanPredicateNestedTest.rangeBooleanPredicateComposeContinue, BooleanPredicateNestedTest.rangeBooleanPredicateComposeContinue, true),
    (`BooleanPredicateNestedTest.rangeBooleanPredicateComposeOuter, BooleanPredicateNestedTest.rangeBooleanPredicateComposeOuter, true),
    (`BooleanPredicateNestedTest.rangeBooleanPredicateComposeOuterCapture, BooleanPredicateNestedTest.rangeBooleanPredicateComposeOuterCapture, true)]
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
      else BooleanPredicateNestedTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate nested-call IR comparisons passed"
