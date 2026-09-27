import LeanExe.Extract.ScalarFunc

namespace PredicateOuterFlagTest

def rangePredicateOuterFlagWord (count seed : UInt64) : Bool := Id.run do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f a then break
    a := a + i.toUInt64 + 1
  return f a

def rangePredicateOuterFlagBoolean (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (a == 0) then break
    a := a + i.toUInt64 + 1
  return f (a == seed)

def rangePredicateOuterFlagWrapped (count seed : UInt64) : Id Bool := do
  let f := fun b : Bool => Id.run do
    let g := fun n : UInt64 => n == seed || b
    return g count && g 0
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if f (a == 0) then break
  return f (a == seed)

def rangePredicateOuterFlagUnused (count seed : UInt64) : Bool := Id.run do
  let _unused := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (count == 0) && g (seed == 0))
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a == seed

def rangePredicateOuterFlagCapture (count seed : UInt64) : Bool := Id.run do
  let p := fun n : UInt64 => n % 5 == 0
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (i.toUInt64 == 0) then continue
    a := a + i.toUInt64 + 1
    if f (a == seed) then break
  return f (a == seed)

def rangePredicateOuterFlagBound (count seed : UInt64) : Bool := Id.run do
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (count == 0))
  let mut a := seed
  for i in [:(count + (f seed).toUInt64).toNat] do
    if f a then continue
    a := a * 3 + i.toUInt64 + 1
  return f a

def rangePredicateOuterFlagNested (count seed : UInt64) : Bool := Id.run do
  let f := fun n : UInt64 => (let g := fun b : Bool => (let h := fun k : UInt64 => k == n || b; h count && h seed); g (n % 3 == 0) || g (seed == 0))
  let mut a := seed
  for i in [:count.toNat] do
    if f a then break
    a := a + i.toUInt64 + 1
  return f a

def rangePredicateOuterFlagId (count seed : UInt64) : Id Bool := do
  let f := fun n : Id UInt64 => Id.run do
    let g := fun k : UInt64 => k == seed
    return g (Id.run n) || g count
  let mut a := seed
  for i in [:count.toNat] do
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return f a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PredicateOuterFlagTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PredicateOuterFlagTest.rangePredicateOuterFlagWord, (fun (x y : UInt64) => (PredicateOuterFlagTest.rangePredicateOuterFlagWord x y).toUInt64), true),
    (`PredicateOuterFlagTest.rangePredicateOuterFlagBoolean, (fun (x y : UInt64) => (PredicateOuterFlagTest.rangePredicateOuterFlagBoolean x y).toUInt64), true),
    (`PredicateOuterFlagTest.rangePredicateOuterFlagWrapped, (fun (x y : UInt64) => (PredicateOuterFlagTest.rangePredicateOuterFlagWrapped x y).toUInt64), true),
    (`PredicateOuterFlagTest.rangePredicateOuterFlagUnused, (fun (x y : UInt64) => (PredicateOuterFlagTest.rangePredicateOuterFlagUnused x y).toUInt64), true),
    (`PredicateOuterFlagTest.rangePredicateOuterFlagCapture, (fun (x y : UInt64) => (PredicateOuterFlagTest.rangePredicateOuterFlagCapture x y).toUInt64), true),
    (`PredicateOuterFlagTest.rangePredicateOuterFlagBound, (fun (x y : UInt64) => (PredicateOuterFlagTest.rangePredicateOuterFlagBound x y).toUInt64), true),
    (`PredicateOuterFlagTest.rangePredicateOuterFlagNested, (fun (x y : UInt64) => (PredicateOuterFlagTest.rangePredicateOuterFlagNested x y).toUInt64), true),
    (`PredicateOuterFlagTest.rangePredicateOuterFlagId, (fun (x y : UInt64) => (PredicateOuterFlagTest.rangePredicateOuterFlagId x y).toUInt64), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean-result outer predicate body extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PredicateOuterFlagTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-result outer predicate body IR comparisons passed"
