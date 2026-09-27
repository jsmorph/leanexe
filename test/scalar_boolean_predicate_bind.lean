import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateBindTest

def booleanPredicateBind (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b && x != 0
  let flag ← pure (f (x == y))
  return if flag then x + 7 else y + 11

def booleanPredicateBindNested (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || x == 0
  let flag ← Id.run (pure (f (x == y)))
  let next ← pure (Id.run (pure (f (!flag))))
  return flag.toUInt64 + next.toUInt64 * 3

def booleanPredicateBindChoice (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b
  let g := fun b : Bool => b && y != 0
  let flag ← pure (if f (x == y) = g false then g true else f false)
  let next ← pure (if _h : x < y then f flag else g flag)
  return if _h : next then x + flag.toUInt64 else y - flag.toUInt64

def booleanPredicateBindCapture (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || y == 0
  let saved ← pure (f (x == y))
  let g := fun z : UInt64 => if saved then z + x else z - y
  let saved ← pure (f (!saved))
  return g y + saved.toUInt64

def booleanPredicateBindUnused (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || x / y == 0
  let _unused ← pure (f true)
  let flag ← f (x == y)
  return if flag then x + y else x - y

def booleanPredicateBindBody (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b || x == 0
  let g : UInt64 → Id UInt64 := fun z => do
    let flag ← pure (f (z == y))
    return if flag then z + 7 else z - 11
  Id.run (g x) + Id.run (g y)

def rangeBooleanPredicateBindStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let delta := Id.run do
      let flag ← pure (f (UInt64.ofNat i % 3 == 0))
      return if flag then 3 else 1
    a := a + delta + UInt64.ofNat i
    if a % 7 == 0 then break
  return a

def rangeBooleanPredicateBindCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => !b || a == seed
    if (Id.run do
      let flag ← pure (f (UInt64.ofNat i % 3 == 0))
      return flag.toUInt64) == 0 then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateBindOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let extra := Id.run do
    let flag ← pure (f (count == 0))
    return flag.toUInt64
  let mut a := seed + extra
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if a % 7 == 0 then break
  let last := Id.run do
    let flag ← pure (f (a == seed))
    return if flag then a + 3 else a
  return last

def rangeBooleanPredicateBindOuterCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b && seed != 0
  let h : UInt64 → Id UInt64 := fun value => do
    let saved ← Id.run (pure (f (value == seed)))
    return if saved then value + 3 else value - 1
  let mut a := seed
  for i in [:count.toNat] do
    a := Id.run (h a) + UInt64.ofNat i
    if a % 11 == 0 then break
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateBindTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateBindTest.booleanPredicateBind, BooleanPredicateBindTest.booleanPredicateBind, false),
    (`BooleanPredicateBindTest.booleanPredicateBindNested, BooleanPredicateBindTest.booleanPredicateBindNested, false),
    (`BooleanPredicateBindTest.booleanPredicateBindChoice, BooleanPredicateBindTest.booleanPredicateBindChoice, false),
    (`BooleanPredicateBindTest.booleanPredicateBindCapture, BooleanPredicateBindTest.booleanPredicateBindCapture, false),
    (`BooleanPredicateBindTest.booleanPredicateBindUnused, BooleanPredicateBindTest.booleanPredicateBindUnused, false),
    (`BooleanPredicateBindTest.booleanPredicateBindBody, BooleanPredicateBindTest.booleanPredicateBindBody, false),
    (`BooleanPredicateBindTest.rangeBooleanPredicateBindStep, BooleanPredicateBindTest.rangeBooleanPredicateBindStep, true),
    (`BooleanPredicateBindTest.rangeBooleanPredicateBindCondition, BooleanPredicateBindTest.rangeBooleanPredicateBindCondition, true),
    (`BooleanPredicateBindTest.rangeBooleanPredicateBindOuter, BooleanPredicateBindTest.rangeBooleanPredicateBindOuter, true),
    (`BooleanPredicateBindTest.rangeBooleanPredicateBindOuterCapture, BooleanPredicateBindTest.rangeBooleanPredicateBindOuterCapture, true)]
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
      else BooleanPredicateBindTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate bind IR comparisons passed"
