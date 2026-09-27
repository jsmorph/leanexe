import LeanExe.Extract.ScalarFunc

namespace LocalNotTest

def localNotFlag (x y : UInt64) : UInt64 :=
  let flag := x == y
  if ¬ flag then x + 3 else y + 7

def localNotCall (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if ¬ f (x == 0) then x + 1 else y + 2

def localNotNested (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n != x
  if _h : ¬ ¬ ¬ f y then x + y else x - y

def localNotDecision (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let flag := decide (¬ (if x < y then f true else f false))
  flag.toUInt64 + x

def localNotLet (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  if ¬ (Id.run (let saved := f (x == 0); f (!saved))) then x + 1 else y + 2

def localNotHelper (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => if ¬ f b then !b else b
  (g true).toUInt64 + (g false).toUInt64 + y

def rangeLocalNotStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != 0
    if ¬ f (i.toUInt64 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangeLocalNotContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => n != seed
    if ¬ f a then
      a := a + 3
      continue
    a := a + i.toUInt64 + 1
  return a

def rangeLocalNotOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let flag := f true
  let mut a := if ¬ flag then seed + 1 else seed
  for i in [:count.toNat] do
    if ¬ (f (a == 0) || f (i.toUInt64 == seed)) then a := a + 2 else a := a + 1
  return a + (decide (¬ f true)).toUInt64

def rangeLocalNotHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if ¬ f b then !b else b
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ ¬ g (a == 0) then break
    a := a + (f (g true)).toUInt64 + i.toUInt64 + 1
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end LocalNotTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`LocalNotTest.localNotFlag, LocalNotTest.localNotFlag, false),
    (`LocalNotTest.localNotCall, LocalNotTest.localNotCall, false),
    (`LocalNotTest.localNotNested, LocalNotTest.localNotNested, false),
    (`LocalNotTest.localNotDecision, LocalNotTest.localNotDecision, false),
    (`LocalNotTest.localNotLet, LocalNotTest.localNotLet, false),
    (`LocalNotTest.localNotHelper, LocalNotTest.localNotHelper, false),
    (`LocalNotTest.rangeLocalNotStep, LocalNotTest.rangeLocalNotStep, true),
    (`LocalNotTest.rangeLocalNotContinue, LocalNotTest.rangeLocalNotContinue, true),
    (`LocalNotTest.rangeLocalNotOuter, LocalNotTest.rangeLocalNotOuter, true),
    (`LocalNotTest.rangeLocalNotHelper, LocalNotTest.rangeLocalNotHelper, true)]
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
      else LocalNotTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/local-not IR comparisons passed"
