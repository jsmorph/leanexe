import LeanExe.Extract.ScalarFunc

namespace BooleanResultBindTest

def booleanResultBindBool (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (Id.run do
    let saved ← pure (f (x == 0))
    return f (!saved)).toUInt64 + y

def booleanResultBindWord (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  (Id.run do
    let saved ← pure (x + (f true).toUInt64)
    return f (saved == y)).toUInt64 + x

def booleanResultBindNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (Id.run do
    let saved ← pure (f (x == 0))
    let word ← pure (x + saved.toUInt64)
    let saved ← pure (f (word == y))
    return f (!saved)).toUInt64 + y

def booleanResultBindCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => Id.run do
    let saved ← pure (f b)
    return f (!saved)
  (g (x == 0)).toUInt64 + (g true).toUInt64

def booleanResultBindUnused (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  (Id.run do
    let _saved ← pure (f (x == 0))
    let _word ← pure (x + y)
    return f true).toUInt64 + x

def booleanResultBindCondition (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  if Id.run (do let saved ← pure (f (x == 0)); return f (!saved)) then x + 3 else y + 7

def rangeBooleanResultBindStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    a := a + (Id.run do
      let saved ← pure (f (i.toUInt64 == seed))
      return f (!saved)).toUInt64 + 1
  return a

def rangeBooleanResultBindCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    if Id.run (do let saved ← pure (a + i.toUInt64); return f (saved != seed)) then break
    a := a + i.toUInt64 + 1
  return a

def rangeBooleanResultBindOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved := Id.run do
    let flag ← pure (f true)
    return f (!flag)
  let mut a := seed + saved.toUInt64
  for i in [:count.toNat] do
    if Id.run (do let flag ← pure (f (a == i.toUInt64)); return f (!flag)) then
      a := a + 3
      continue
    a := a + 1
  return a + saved.toUInt64

def rangeBooleanResultBindHelper (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun n : UInt64 => Id.run do
    let saved ← pure (n + seed)
    return f (saved == 0)
  let mut a := seed
  for i in [:count.toNat] do
    let h := fun n : UInt64 => Id.run do
      let saved ← pure (n + a)
      return g saved
    if h i.toUInt64 then break
    a := a + (g a).toUInt64 + 1
  return a + (g seed).toUInt64

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanResultBindTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanResultBindTest.booleanResultBindBool, BooleanResultBindTest.booleanResultBindBool, false),
    (`BooleanResultBindTest.booleanResultBindWord, BooleanResultBindTest.booleanResultBindWord, false),
    (`BooleanResultBindTest.booleanResultBindNested, BooleanResultBindTest.booleanResultBindNested, false),
    (`BooleanResultBindTest.booleanResultBindCapture, BooleanResultBindTest.booleanResultBindCapture, false),
    (`BooleanResultBindTest.booleanResultBindUnused, BooleanResultBindTest.booleanResultBindUnused, false),
    (`BooleanResultBindTest.booleanResultBindCondition, BooleanResultBindTest.booleanResultBindCondition, false),
    (`BooleanResultBindTest.rangeBooleanResultBindStep, BooleanResultBindTest.rangeBooleanResultBindStep, true),
    (`BooleanResultBindTest.rangeBooleanResultBindCondition, BooleanResultBindTest.rangeBooleanResultBindCondition, true),
    (`BooleanResultBindTest.rangeBooleanResultBindOuter, BooleanResultBindTest.rangeBooleanResultBindOuter, true),
    (`BooleanResultBindTest.rangeBooleanResultBindHelper, BooleanResultBindTest.rangeBooleanResultBindHelper, true)]
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
      else BooleanResultBindTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean result-bind IR comparisons passed"
