import LeanExe.Extract.ScalarFunc

namespace BooleanScopeBindTest

def booleanScopeBindWord (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (x + y) : Id UInt64)
    let f := fun n : Id UInt64 => (Id.run n) == saved
    return f x || f y).toUInt64 + x

def booleanScopeBindFlag (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (x == y) : Id Bool)
    let f := fun b : Id Bool => Id.run b || saved
    return f (x == 0) && f (y == 0)).toUInt64 + y

def booleanScopeBindNested (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (x + y) : Id UInt64)
    let flag ← (pure (saved == y) : Id Bool)
    let f := fun n : UInt64 => flag || n == saved
    return f x && f y).toUInt64 + x

def booleanScopeBindRetained (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (pure (pure (x + y)) : Id (Id UInt64))
    let f := fun n : UInt64 => n == Id.run saved
    return f x || f y).toUInt64 + y

def booleanScopeBindUnused (x y : UInt64) : UInt64 :=
  (Id.run do
    let _unused ← (pure (x == y) : Id Bool)
    let f := fun n : UInt64 => n == y
    return f x || f 0).toUInt64 + x

def booleanScopeBindChoice (x y : UInt64) : UInt64 :=
  (Id.run do
    let saved ← (if x == 0 then pure y else pure (x + y) : Id UInt64)
    let f := fun n : UInt64 => n == saved
    return f x || f y).toUInt64 + y

def rangeBooleanScopeBindStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (Id.run do
      let saved ← (pure (a + i.toUInt64) : Id UInt64)
      let f := fun n : Id UInt64 => Id.run n == saved
      return f i.toUInt64 || f seed).toUInt64
  return a

def rangeBooleanScopeBindExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if (Id.run do
      let saved ← (pure (a == seed) : Id Bool)
      let f := fun b : Id Bool => Id.run b || saved
      return f (a == 7) && f (i.toUInt64 == seed)) then break
  return a

def rangeBooleanScopeBindContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (Id.run do
      let saved ← (pure (pure (a + seed)) : Id (Id UInt64))
      let f := fun n : UInt64 => n == Id.run saved
      return f i.toUInt64 || f seed) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeBooleanScopeBindTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (Id.run do
    let saved ← (pure (pure (a == seed)) : Id (Id Bool))
    let f := fun b : Bool => b != Id.run saved
    return f (a == 0) || f (seed == 0)).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanScopeBindTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanScopeBindTest.booleanScopeBindWord, (fun (x y : UInt64) => BooleanScopeBindTest.booleanScopeBindWord x y), false),
    (`BooleanScopeBindTest.booleanScopeBindFlag, (fun (x y : UInt64) => BooleanScopeBindTest.booleanScopeBindFlag x y), false),
    (`BooleanScopeBindTest.booleanScopeBindNested, (fun (x y : UInt64) => BooleanScopeBindTest.booleanScopeBindNested x y), false),
    (`BooleanScopeBindTest.booleanScopeBindRetained, (fun (x y : UInt64) => BooleanScopeBindTest.booleanScopeBindRetained x y), false),
    (`BooleanScopeBindTest.booleanScopeBindUnused, (fun (x y : UInt64) => BooleanScopeBindTest.booleanScopeBindUnused x y), false),
    (`BooleanScopeBindTest.booleanScopeBindChoice, (fun (x y : UInt64) => BooleanScopeBindTest.booleanScopeBindChoice x y), false),
    (`BooleanScopeBindTest.rangeBooleanScopeBindStep, (fun (x y : UInt64) => BooleanScopeBindTest.rangeBooleanScopeBindStep x y), true),
    (`BooleanScopeBindTest.rangeBooleanScopeBindExit, (fun (x y : UInt64) => BooleanScopeBindTest.rangeBooleanScopeBindExit x y), true),
    (`BooleanScopeBindTest.rangeBooleanScopeBindContinue, (fun (x y : UInt64) => BooleanScopeBindTest.rangeBooleanScopeBindContinue x y), true),
    (`BooleanScopeBindTest.rangeBooleanScopeBindTail, (fun (x y : UInt64) => BooleanScopeBindTest.rangeBooleanScopeBindTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: general Boolean scope bind extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanScopeBindTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/general Boolean scope bind IR comparisons passed"
