import LeanExe.Extract.ScalarFunc

namespace BooleanScopeApplicationTest

def booleanScopeApplicationWord (x y : UInt64) : UInt64 :=
  ((fun saved : UInt64 =>
    let f := fun n : UInt64 => n == saved
    f x || f y) (x + y)).toUInt64 + x

def booleanScopeApplicationFlag (x y : UInt64) : UInt64 :=
  ((fun saved : Bool =>
    let f := fun b : Bool => b || saved
    f (x == 0) && f (y == 0)) (x == y)).toUInt64 + y

def booleanScopeApplicationNested (x y : UInt64) : UInt64 :=
  ((fun saved : UInt64 =>
    (fun flag : Bool =>
      let f := fun n : UInt64 => flag || n == saved
      f x && f y) (saved == y)) (x + y)).toUInt64 + x

def booleanScopeApplicationRetained (x y : UInt64) : UInt64 :=
  ((fun saved : Id (Id UInt64) =>
    let f := fun n : UInt64 => n == Id.run (Id.run saved)
    f x || f y) (pure (pure (x + y)))).toUInt64 + y

def booleanScopeApplicationUnused (x y : UInt64) : UInt64 :=
  ((fun _unused : Bool =>
    let f := fun n : UInt64 => n == y
    f x || f 0) (x == y)).toUInt64 + x

def booleanScopeApplicationChoice (x y : UInt64) : UInt64 :=
  ((fun saved : UInt64 =>
    let f := fun n : UInt64 => n == saved
    f x || f y) (if x == 0 then y else x + y)).toUInt64 + y

def rangeBooleanScopeApplicationStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + ((fun saved : UInt64 =>
      let f := fun n : Id UInt64 => Id.run n == saved
      f i.toUInt64 || f seed) (a + i.toUInt64)).toUInt64
  return a

def rangeBooleanScopeApplicationExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if ((fun saved : Bool =>
      let f := fun b : Id Bool => Id.run b || saved
      f (a == 7) && f (i.toUInt64 == seed)) (a == seed)) then break
  return a

def rangeBooleanScopeApplicationContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if ((fun saved : Id (Id UInt64) =>
      let f := fun n : UInt64 => n == Id.run (Id.run saved)
      f i.toUInt64 || f seed) (pure (pure (a + seed)))) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBooleanScopeApplicationTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + ((fun saved : Id (Id Bool) =>
    let f := fun b : Bool => b != Id.run (Id.run saved)
    f (a == 0) || f (seed == 0)) (pure (pure (a == seed)))).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanScopeApplicationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanScopeApplicationTest.booleanScopeApplicationWord, (fun (x y : UInt64) => BooleanScopeApplicationTest.booleanScopeApplicationWord x y), false),
    (`BooleanScopeApplicationTest.booleanScopeApplicationFlag, (fun (x y : UInt64) => BooleanScopeApplicationTest.booleanScopeApplicationFlag x y), false),
    (`BooleanScopeApplicationTest.booleanScopeApplicationNested, (fun (x y : UInt64) => BooleanScopeApplicationTest.booleanScopeApplicationNested x y), false),
    (`BooleanScopeApplicationTest.booleanScopeApplicationRetained, (fun (x y : UInt64) => BooleanScopeApplicationTest.booleanScopeApplicationRetained x y), false),
    (`BooleanScopeApplicationTest.booleanScopeApplicationUnused, (fun (x y : UInt64) => BooleanScopeApplicationTest.booleanScopeApplicationUnused x y), false),
    (`BooleanScopeApplicationTest.booleanScopeApplicationChoice, (fun (x y : UInt64) => BooleanScopeApplicationTest.booleanScopeApplicationChoice x y), false),
    (`BooleanScopeApplicationTest.rangeBooleanScopeApplicationStep, (fun (x y : UInt64) => BooleanScopeApplicationTest.rangeBooleanScopeApplicationStep x y), true),
    (`BooleanScopeApplicationTest.rangeBooleanScopeApplicationExit, (fun (x y : UInt64) => BooleanScopeApplicationTest.rangeBooleanScopeApplicationExit x y), true),
    (`BooleanScopeApplicationTest.rangeBooleanScopeApplicationContinue, (fun (x y : UInt64) => BooleanScopeApplicationTest.rangeBooleanScopeApplicationContinue x y), true),
    (`BooleanScopeApplicationTest.rangeBooleanScopeApplicationTail, (fun (x y : UInt64) => BooleanScopeApplicationTest.rangeBooleanScopeApplicationTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: general Boolean scope application extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanScopeApplicationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/general Boolean scope application IR comparisons passed"
