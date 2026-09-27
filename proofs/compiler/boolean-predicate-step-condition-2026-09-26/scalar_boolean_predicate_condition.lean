import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateConditionTest

def booleanPredicateCondition (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  if f (x == y) then x + 3 else if g false then y * 5 else x - y

def booleanPredicateConditionRelations (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  let a := if f (x == y) = g true then x + y else x - y
  let b := if f false ≠ g (x == 0) then x * 3 else y * 5
  if f true == g false then a + b else if f false != g true then a - b else a

def booleanPredicateConditionDependent (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  if _h : f (x == y) then
    if _k : f false = g true then x + 7 else y - 11
  else
    if _k : f true ≠ g false then x ^^^ y else x * y

def booleanPredicateConditionNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || y == 0
  let g := fun b : Bool => !b && x != y
  if !(f (g (x == y))) && g true then x + 3
  else if (if _h : x < y then f false else g true) then y + 5
  else if (if f false then g true else f true) then x - 7 else y - 11

def booleanPredicateConditionCapture (x y : UInt64) : UInt64 :=
  let saved := x == y
  let f := fun b : Bool => b || saved
  let h := fun a : UInt64 => if f (a == y) then a + x else a - x
  let x := x + 1
  let g := fun b : Bool => (if f b then x else y) == x
  if g (x == y) = f saved then h x else h y

def booleanPredicateConditionBody (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let g := fun b : Bool => (if @Eq Bool (f b) true then x else y) == x
  let a ← if @Eq Bool (f (x == y)) true then pure (x + 1) else pure (y + 3)
  let b := if g false then x - y else y - x
  return if _h : @Ne Bool (f true) (f false) then a + b else a - b

def rangeBooleanPredicateConditionStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    a := a + (if f (UInt64.ofNat i % 2 == 0) then 3 else 1)
    if (if f (a % 7 == 0) then 1 else 0 : UInt64) == 1 then break
  return a

def rangeBooleanPredicateConditionContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (if _h : f (UInt64.ofNat i % 3 == 0) ≠ f false then 1 else 0 : UInt64) == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateConditionOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let stop := count + (if f false then 1 else 0)
  let mut a := seed + (if _h : f true = f false then 1 else 0)
  for i in [:stop.toNat] do
    if (if f (a % 7 == 0) then 1 else 0 : UInt64) == 1 then break
    a := a + UInt64.ofNat i + 1
  return if f (a == seed) then a + 1 else a

def rangeBooleanPredicateConditionOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (if f b then (1 : UInt64) else 0) == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (if g b = f b then (1 : UInt64) else 0) == 1 && a != seed
    if (if h (a % 5 == 0) then 1 else 0 : UInt64) == 1 then break
    a := a + UInt64.ofNat i + 1
  return if _h : g (a == seed) ≠ f false then a + 1 else a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateConditionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateConditionTest.booleanPredicateCondition, BooleanPredicateConditionTest.booleanPredicateCondition, false),
    (`BooleanPredicateConditionTest.booleanPredicateConditionRelations, BooleanPredicateConditionTest.booleanPredicateConditionRelations, false),
    (`BooleanPredicateConditionTest.booleanPredicateConditionDependent, BooleanPredicateConditionTest.booleanPredicateConditionDependent, false),
    (`BooleanPredicateConditionTest.booleanPredicateConditionNested, BooleanPredicateConditionTest.booleanPredicateConditionNested, false),
    (`BooleanPredicateConditionTest.booleanPredicateConditionCapture, BooleanPredicateConditionTest.booleanPredicateConditionCapture, false),
    (`BooleanPredicateConditionTest.booleanPredicateConditionBody, BooleanPredicateConditionTest.booleanPredicateConditionBody, false),
    (`BooleanPredicateConditionTest.rangeBooleanPredicateConditionStep, BooleanPredicateConditionTest.rangeBooleanPredicateConditionStep, true),
    (`BooleanPredicateConditionTest.rangeBooleanPredicateConditionContinue, BooleanPredicateConditionTest.rangeBooleanPredicateConditionContinue, true),
    (`BooleanPredicateConditionTest.rangeBooleanPredicateConditionOuter, BooleanPredicateConditionTest.rangeBooleanPredicateConditionOuter, true),
    (`BooleanPredicateConditionTest.rangeBooleanPredicateConditionOuterCapture, BooleanPredicateConditionTest.rangeBooleanPredicateConditionOuterCapture, true)]
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
      else BooleanPredicateConditionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate condition IR comparisons passed"
