import LeanExe.Extract.ScalarFunc

namespace BooleanScopeBindingTest

def booleanScopeBindingWord (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let f := fun n : Id UInt64 =>
     let g := fun b : Id Bool => (Id.run b) != (saved == y)
     g ((Id.run n) == saved) || g (x == 0)
   f x && f y).toUInt64 + y

def booleanScopeBindingFlag (x y : UInt64) : UInt64 :=
  (let saved := x == y
   let f := fun n : UInt64 => saved || n == y
   f x && f 0).toUInt64 + x

def booleanScopeBindingWordId (x y : UInt64) : UInt64 :=
  (let saved : Id (Id UInt64) := pure (pure (x + y))
   let f := fun n : Id UInt64 => (Id.run n) == Id.run (Id.run saved)
   f x || f y).toUInt64 + y

def booleanScopeBindingFlagId (x y : UInt64) : UInt64 :=
  (let saved : Id (Id Bool) := pure (pure (x == y))
   let f := fun b : Id Bool => Id.run b || Id.run (Id.run saved)
   f (x == 0) && f (y == 0)).toUInt64 + x

def booleanScopeBindingUnused (x y : UInt64) : UInt64 :=
  (let _unused := x + y
   let f := fun n : UInt64 => n == y
   f x || f 0).toUInt64 + x

def booleanScopeBindingNested (x y : UInt64) : UInt64 :=
  (let saved := x + y
   let flag := saved == x
   let f := fun n : UInt64 => flag || n == saved
   f x && f y).toUInt64 + y

def rangeBooleanScopeBindingStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (let saved := a + i.toUInt64
              let f := fun n : Id UInt64 => (Id.run n) == saved
              f i.toUInt64 || f seed).toUInt64
  return a

def rangeBooleanScopeBindingExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (let saved := a == seed
        let f := fun b : Id Bool => Id.run b || saved
        f (a == 7) && f (i.toUInt64 == seed)) then break
  return a

def rangeBooleanScopeBindingContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let saved : Id (Id UInt64) := pure (pure (a + seed))
        let f := fun n : UInt64 => n == Id.run (Id.run saved)
        f i.toUInt64 || f seed) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBooleanScopeBindingTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (let saved : Id (Id Bool) := pure (pure (a == seed))
              let f := fun b : Bool => b != Id.run (Id.run saved)
              f (a == 0) || f (seed == 0)).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanScopeBindingTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanScopeBindingTest.booleanScopeBindingWord, (fun (x y : UInt64) => BooleanScopeBindingTest.booleanScopeBindingWord x y), false),
    (`BooleanScopeBindingTest.booleanScopeBindingFlag, (fun (x y : UInt64) => BooleanScopeBindingTest.booleanScopeBindingFlag x y), false),
    (`BooleanScopeBindingTest.booleanScopeBindingWordId, (fun (x y : UInt64) => BooleanScopeBindingTest.booleanScopeBindingWordId x y), false),
    (`BooleanScopeBindingTest.booleanScopeBindingFlagId, (fun (x y : UInt64) => BooleanScopeBindingTest.booleanScopeBindingFlagId x y), false),
    (`BooleanScopeBindingTest.booleanScopeBindingUnused, (fun (x y : UInt64) => BooleanScopeBindingTest.booleanScopeBindingUnused x y), false),
    (`BooleanScopeBindingTest.booleanScopeBindingNested, (fun (x y : UInt64) => BooleanScopeBindingTest.booleanScopeBindingNested x y), false),
    (`BooleanScopeBindingTest.rangeBooleanScopeBindingStep, (fun (x y : UInt64) => BooleanScopeBindingTest.rangeBooleanScopeBindingStep x y), true),
    (`BooleanScopeBindingTest.rangeBooleanScopeBindingExit, (fun (x y : UInt64) => BooleanScopeBindingTest.rangeBooleanScopeBindingExit x y), true),
    (`BooleanScopeBindingTest.rangeBooleanScopeBindingContinue, (fun (x y : UInt64) => BooleanScopeBindingTest.rangeBooleanScopeBindingContinue x y), true),
    (`BooleanScopeBindingTest.rangeBooleanScopeBindingTail, (fun (x y : UInt64) => BooleanScopeBindingTest.rangeBooleanScopeBindingTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: general Boolean scope binding extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanScopeBindingTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/general Boolean scope binding IR comparisons passed"
