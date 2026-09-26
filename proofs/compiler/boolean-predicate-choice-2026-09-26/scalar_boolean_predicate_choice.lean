import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateChoiceTest

def booleanPredicateChoice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  (if f (x == y) then f false else g true).toUInt64 +
    (if g false = f true then g (x == 0) else f (y == 0)).toUInt64 * 3

def booleanPredicateChoiceDependent (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  (if _h : f (x == 0) ≠ g (x == y) then f false else !(g true)).toUInt64 +
    (if _h : g false then !(f true) else g (f false)).toUInt64

def booleanPredicateChoiceNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  (!(if f (x == y) then
    (if _h : g true = f false then g false else f true)
    else g (x == 0) && f (y == 0))).toUInt64

def booleanPredicateChoiceArgument (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  (f (if g (x == 0) then f false else g true)).toUInt64 +
    (!(g (if _h : f true ≠ g false then g (f false) else f (g true)))).toUInt64

def booleanPredicateChoiceBranches (x y : UInt64) : UInt64 :=
  let saved := x == y
  let f := fun b : Bool => b || saved
  let y := y + 1
  let g := fun b : Bool => !b && x == y
  (if saved then f true else g false).toUInt64 +
    (if _h : x != y then g true else f false).toUInt64 * 3

def booleanPredicateChoiceBody (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let g := fun b : Bool => Bool.toUInt64 (if @Eq Bool (f b) true then f false else f true) == x
  let a ← pure (if g (x == y) then g false else !(f true)).toUInt64
  let b ← pure (!(if _h : g true then f false else g (f true))).toUInt64
  return a + b

def rangeBooleanPredicateChoiceStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => !b && a != seed
    a := a + UInt64.ofNat i
    if (if f (a % 7 == 0) then g (a == seed) else f true).toUInt64 == 1 then break
  return a

def rangeBooleanPredicateChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (!(if _h : f (UInt64.ofNat i % 3 == 0) then f (a == seed) else f true)).toUInt64 == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let stop := count + (if f false then g true else f true).toUInt64
  let mut a := seed + (if _h : g false = f true then f false else g false).toUInt64
  for i in [:stop.toNat] do
    if (!(if f (a % 7 == 0) then g (a == seed) else f true)).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (if _h : g (f (a == seed)) ≠ f false then f true else g false).toUInt64

def rangeBooleanPredicateChoiceOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (!(if _h : f b then f (!b) else f b)).toUInt64 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (if g b then f b else g false).toUInt64 == 1 && a != seed
    if (if h (a % 5 == 0) then g (a == seed) else h true).toUInt64 == 1 then break
    a := a + UInt64.ofNat i + 1
  return a + (!(if _h : g (a == seed) then f true else g false)).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateChoiceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateChoiceTest.booleanPredicateChoice, BooleanPredicateChoiceTest.booleanPredicateChoice, false),
    (`BooleanPredicateChoiceTest.booleanPredicateChoiceDependent, BooleanPredicateChoiceTest.booleanPredicateChoiceDependent, false),
    (`BooleanPredicateChoiceTest.booleanPredicateChoiceNested, BooleanPredicateChoiceTest.booleanPredicateChoiceNested, false),
    (`BooleanPredicateChoiceTest.booleanPredicateChoiceArgument, BooleanPredicateChoiceTest.booleanPredicateChoiceArgument, false),
    (`BooleanPredicateChoiceTest.booleanPredicateChoiceBranches, BooleanPredicateChoiceTest.booleanPredicateChoiceBranches, false),
    (`BooleanPredicateChoiceTest.booleanPredicateChoiceBody, BooleanPredicateChoiceTest.booleanPredicateChoiceBody, false),
    (`BooleanPredicateChoiceTest.rangeBooleanPredicateChoiceStep, BooleanPredicateChoiceTest.rangeBooleanPredicateChoiceStep, true),
    (`BooleanPredicateChoiceTest.rangeBooleanPredicateChoiceContinue, BooleanPredicateChoiceTest.rangeBooleanPredicateChoiceContinue, true),
    (`BooleanPredicateChoiceTest.rangeBooleanPredicateChoiceOuter, BooleanPredicateChoiceTest.rangeBooleanPredicateChoiceOuter, true),
    (`BooleanPredicateChoiceTest.rangeBooleanPredicateChoiceOuterCapture, BooleanPredicateChoiceTest.rangeBooleanPredicateChoiceOuterCapture, true)]
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
      else BooleanPredicateChoiceTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate choice IR comparisons passed"
