import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateLetTest

def booleanPredicateLet (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let g := fun b : Bool => b || y == 0
  let first := f (x == y)
  let second := g first && !(f false)
  if first || second then x + second.toUInt64 else y - first.toUInt64

def booleanPredicateLetNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => b && y != 0
  let flag := !!!(f (g (f (x == y))))
  let flag := g flag != f (!flag)
  if _h : flag then x + y else x - y

def booleanPredicateLetChoice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || y == 0
  let g := fun b : Bool => b && x != y
  let first := if f (x == y) then g true else !(f false)
  let second := if _h : x < y ∧ (g first).toUInt64 ≠ 0 then f first else g (!first)
  let third := decide (f second ≠ g first)
  if second && third then x * 3 else y + first.toUInt64

def booleanPredicateLetCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let saved := f (x == 0)
  let h := fun a : UInt64 =>
    let inner := f (a == y) && saved
    if inner then a + x else a - x
  let x := x + 1
  let saved := f (x == y)
  if saved then h x else h y

def booleanPredicateLetUnused (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != 0
  let _unused := f (x == y)
  let kept := f true
  let _unused := if False then f kept else !(f false)
  x + y + kept.toUInt64

def booleanPredicateLetBody (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let flag : Id (Id Bool) := f (x == y)
  let g := fun b : Bool => (let saved := f b; Bool.toUInt64 saved) == x
  let result := g flag
  return if result then Bool.toUInt64 flag + x else y

def rangeBooleanPredicateLetStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    a := a + (let flag := f (UInt64.ofNat i % 2 == 0); if flag then 3 else 1)
    if (let stop := f (a % 7 == 0); stop.toUInt64) == 1 then break
  return a

def rangeBooleanPredicateLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if (let skip := !(f (UInt64.ofNat i % 3 == 0)); skip.toUInt64) == 1 then continue
    a := a * 3 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let stop := count + (let flag := f false; flag.toUInt64)
  let mut a := seed + (let flag := f true; if flag then 1 else 0)
  for i in [:stop.toNat] do
    if (let flag := f (a % 7 == 0); flag.toUInt64) == 1 then break
    a := a + UInt64.ofNat i + 1
  return let flag := f (a == seed); if flag then a + 1 else a

def rangeBooleanPredicateLetOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => (let flag := !(f b); flag.toUInt64) == 0
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun b : Bool => (let flag := g b && f b; flag.toUInt64) == 1 && a != seed
    if (let flag := h (a % 5 == 0); flag.toUInt64) == 1 then break
    a := a + UInt64.ofNat i + 1
  return let flag := g (a == seed); if flag then a + 1 else a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateLetTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateLetTest.booleanPredicateLet, BooleanPredicateLetTest.booleanPredicateLet, false),
    (`BooleanPredicateLetTest.booleanPredicateLetNested, BooleanPredicateLetTest.booleanPredicateLetNested, false),
    (`BooleanPredicateLetTest.booleanPredicateLetChoice, BooleanPredicateLetTest.booleanPredicateLetChoice, false),
    (`BooleanPredicateLetTest.booleanPredicateLetCapture, BooleanPredicateLetTest.booleanPredicateLetCapture, false),
    (`BooleanPredicateLetTest.booleanPredicateLetUnused, BooleanPredicateLetTest.booleanPredicateLetUnused, false),
    (`BooleanPredicateLetTest.booleanPredicateLetBody, BooleanPredicateLetTest.booleanPredicateLetBody, false),
    (`BooleanPredicateLetTest.rangeBooleanPredicateLetStep, BooleanPredicateLetTest.rangeBooleanPredicateLetStep, true),
    (`BooleanPredicateLetTest.rangeBooleanPredicateLetContinue, BooleanPredicateLetTest.rangeBooleanPredicateLetContinue, true),
    (`BooleanPredicateLetTest.rangeBooleanPredicateLetOuter, BooleanPredicateLetTest.rangeBooleanPredicateLetOuter, true),
    (`BooleanPredicateLetTest.rangeBooleanPredicateLetOuterCapture, BooleanPredicateLetTest.rangeBooleanPredicateLetOuterCapture, true)]
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
      else BooleanPredicateLetTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate let IR comparisons passed"
