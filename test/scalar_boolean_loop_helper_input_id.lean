import LeanExe.Extract.ScalarFunc

namespace BooleanLoopHelperInputIdTest

def rangeBoolHelperInputIdWord (count seed : UInt64) : Bool :=
  let f (x : Id UInt64) := Id.run x + seed + 1
  let value := Id.run do
    let mut a := f (pure seed)
    for i in [:count.toNat] do
      a := f (pure (a + i.toUInt64))
    return a
  f (pure value) == f (pure seed)

def rangeBoolHelperInputIdBooleanWord (count seed : UInt64) : Bool :=
  let f (flag : Id Bool) := seed + (Id.run flag).toUInt64
  let value := Id.run do
    let mut a := f (pure false)
    for i in [:count.toNat] do
      a := a + f (pure (i.toUInt64 % 2 == 0))
    return a
  value == f (pure true)

def rangeBoolHelperInputIdPredicate (count seed : UInt64) : Bool :=
  let f (x : Id UInt64) := Id.run x % 2 == seed % 2
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + (f (pure i.toUInt64)).toUInt64
    return a
  f (pure value)

def rangeBoolHelperInputIdBooleanPredicate (count : UInt64) (flag : Bool) : Bool :=
  let f (input : Id Bool) := Id.run input && flag
  let value := Id.run do
    let mut a := (f (pure true)).toUInt64
    for i in [:count.toNat] do
      a := a + (f (pure (i.toUInt64 % 2 == 0))).toUInt64
    return a
  f (pure (value == count))

def rangeBoolHelperInputIdRepeated (count seed : UInt64) : Id Bool :=
  let f (x : Id (Id (Id UInt64))) : Id (Id UInt64) := pure (pure (Id.run (Id.run (Id.run x)) + seed))
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := Id.run (Id.run (f (pure (pure (pure (a + i.toUInt64))))))
    return a
  pure (value == Id.run (Id.run (f (pure (pure (pure seed))))))

def rangeBoolHelperInputIdBound (count seed : UInt64) : Bool :=
  let f (flag : Id (Id Bool)) := if Id.run (Id.run flag) then count % 17 else count % 5
  let value := Id.run do
    let mut a := seed
    for i in [:(f (pure (pure (seed % 2 == 0)))).toNat] do
      a := a + i.toUInt64 + 1
    return a
  value == seed + f (pure (pure true))

def rangeBoolHelperInputIdExit (count seed : UInt64) : Bool :=
  let f (x : Id (Id UInt64)) : Id Bool := pure (Id.run (Id.run x) % 7 == seed % 7)
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if Id.run (f (pure (pure a))) then break
    return a
  Id.run (f (pure (pure value)))

def rangeBoolHelperInputIdContinue (count seed : UInt64) : Id Bool :=
  let f (flag : Id (Id Bool)) : Id (Id Bool) := pure (pure (Id.run (Id.run flag) || seed == 0))
  let value := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if Id.run (Id.run (f (pure (pure (i.toUInt64 % 2 == 0))))) then continue
      a := a + i.toUInt64 + 1
    return a
  pure (Id.run (Id.run (f (pure (pure (value == seed))))))

def rangeBoolHelperInputIdMixed (count seed : UInt64) : Bool :=
  let f (x : Id UInt64) := Id.run x + seed
  let g (flag : Id Bool) := f (pure (Id.run flag).toUInt64)
  let value := Id.run do
    let mut a := g (pure false)
    for i in [:count.toNat] do
      a := a + g (pure (i.toUInt64 % 2 == 0))
    return a
  value == g (pure true)

def rangeBoolHelperInputIdShadow (count seed : UInt64) : Bool :=
  let f (x : Id UInt64) := Id.run x + seed
  let initial := f (pure 0)
  let f (x : Id (Id UInt64)) := f (pure (Id.run (Id.run x))) + count
  let value := Id.run do
    let mut a := initial
    for i in [:count.toNat] do
      a := f (pure (pure (a + i.toUInt64)))
    return a
  value == f (pure (pure initial))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLoopHelperInputIdTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdWord, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdWord x y).toUInt64), true),
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdBooleanWord, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdBooleanWord x y).toUInt64), true),
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdPredicate, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdPredicate x y).toUInt64), true),
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdBooleanPredicate, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdBooleanPredicate x (y != 0)).toUInt64), true),
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdRepeated, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdRepeated x y).toUInt64), true),
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdBound, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdBound x y).toUInt64), true),
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdExit, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdExit x y).toUInt64), true),
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdContinue, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdContinue x y).toUInt64), true),
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdMixed, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdMixed x y).toUInt64), true),
    (`BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdShadow, (fun (x y : UInt64) => (BooleanLoopHelperInputIdTest.rangeBoolHelperInputIdShadow x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean loop helper-input-id extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLoopHelperInputIdTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean loop helper-input-id IR comparisons passed"
