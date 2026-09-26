import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateEqualityTest

def booleanPredicateEqual (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  (f (x == y) == g false).toUInt64 + (g (x != 0) != f true).toUInt64 * 3

def booleanPredicateDecideEqual (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  (decide (f (x == 0) = g (x == y))).toUInt64 + (decide (g false ≠ f true)).toUInt64 * 3

def booleanPredicateEqualityNot (x y : UInt64) : UInt64 :=
  let saved := x == y
  let f := fun b : Bool => !b || x == 0
  (!(f saved != !(f false && saved))).toUInt64 + (!(decide (f true = saved))).toUInt64

def booleanPredicateEqualityMixed (x y : UInt64) : UInt64 :=
  let word := fun n : UInt64 => n % 3 == 0
  let flag := fun b : Bool => b && y != 0
  (word x == flag (x / y == 0)).toUInt64 + (decide (flag true ≠ word y)).toUInt64 * 3

def booleanPredicateEqualityArgument (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  (f (g (x == 0) == f false)).toUInt64 + (!(g (decide (f true ≠ g false)))).toUInt64

def booleanPredicateEqualityBody (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let g := fun b : Bool => (@BEq.beq Bool (@instBEqOfDecidableEq Bool instDecidableEqBool) (f b) (f (!b))).toUInt64 == x
  let a ← pure (g (x == y) != f (g false)).toUInt64
  let b ← pure (decide (@Eq Bool (f true) (!(g false)))).toUInt64
  return a + b

def rangeBooleanPredicateEqualityStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => !b && a != seed
    a := a + UInt64.ofNat i
    if (f (a % 7 == 0) == g (a == seed)).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateEqualityContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (!(decide (f (UInt64.ofNat i % 3 == 0) ≠ f (a == seed)))).toUInt64 == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateEqualityOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let stop := count + (decide (f false = g true)).toUInt64
  let mut a := seed + (g false != f true).toUInt64
  for i in [:stop.toNat] do
    if (!(f (a % 7 == 0) == g (a == seed))).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (decide (g (f (a == seed)) ≠ f false)).toUInt64

def rangeBooleanPredicateEqualityOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (!(decide (f b = f (!b)))).toUInt64 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (g b != f b).toUInt64 == 1 && a != seed
    if (h (a % 5 == 0) == g (a == seed)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(decide (g (a == seed) ≠ f true))).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateEqualityTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateEqualityTest.booleanPredicateEqual, BooleanPredicateEqualityTest.booleanPredicateEqual, false),
    (`BooleanPredicateEqualityTest.booleanPredicateDecideEqual, BooleanPredicateEqualityTest.booleanPredicateDecideEqual, false),
    (`BooleanPredicateEqualityTest.booleanPredicateEqualityNot, BooleanPredicateEqualityTest.booleanPredicateEqualityNot, false),
    (`BooleanPredicateEqualityTest.booleanPredicateEqualityMixed, BooleanPredicateEqualityTest.booleanPredicateEqualityMixed, false),
    (`BooleanPredicateEqualityTest.booleanPredicateEqualityArgument, BooleanPredicateEqualityTest.booleanPredicateEqualityArgument, false),
    (`BooleanPredicateEqualityTest.booleanPredicateEqualityBody, BooleanPredicateEqualityTest.booleanPredicateEqualityBody, false),
    (`BooleanPredicateEqualityTest.rangeBooleanPredicateEqualityStep, BooleanPredicateEqualityTest.rangeBooleanPredicateEqualityStep, true),
    (`BooleanPredicateEqualityTest.rangeBooleanPredicateEqualityContinue, BooleanPredicateEqualityTest.rangeBooleanPredicateEqualityContinue, true),
    (`BooleanPredicateEqualityTest.rangeBooleanPredicateEqualityOuter, BooleanPredicateEqualityTest.rangeBooleanPredicateEqualityOuter, true),
    (`BooleanPredicateEqualityTest.rangeBooleanPredicateEqualityOuterCapture, BooleanPredicateEqualityTest.rangeBooleanPredicateEqualityOuterCapture, true)]
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
      else BooleanPredicateEqualityTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate equality IR comparisons passed"
