import LeanExe.Extract.ScalarFunc

namespace PredicateOuterBodyTest

def rangePredicateOuterBodyWord (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f a then a := a + i.toUInt64 + 7 else a := a * 3 + 1
  return a

def rangePredicateOuterBodyBoolean (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (a == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyUnused (count seed : UInt64) : Id UInt64 := do
  let _unused := fun b : Bool => (let g := fun n : UInt64 => n % 3 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a

def rangePredicateOuterBodyBound (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (count == 0))
  let mut a := seed
  for i in [:(count + (f seed).toUInt64).toNat] do
    if f a then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyInitial (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed + (f (seed == 0)).toUInt64
  for i in [:count.toNat] do
    if f (a == seed) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyTail (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 5 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if f a then break
  return a + (f a).toUInt64 + (f seed).toUInt64

def rangePredicateOuterBodyCapture (count seed : UInt64) : Id UInt64 := do
  let p := fun n : UInt64 => n % 5 == 0
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (i.toUInt64 == 0) then continue
    a := a + i.toUInt64 + 1
    if f (a == seed) then break
  return a

def rangePredicateOuterBodyWrapped (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => Id.run do
    let g := fun k : Bool => k || count == seed
    return g b && g (seed == 0)
  let mut a := seed
  for i in [:count.toNat] do
    if _h : f (a % 3 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyNested (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun b : Bool => (let h := fun k : UInt64 => k == n || b; h count && h seed); g (n % 3 == 0) || g (seed == 0))
  let mut a := seed
  for i in [:count.toNat] do
    if f a then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyId (count seed : UInt64) : Id UInt64 := do
  let f := fun n : Id UInt64 => Id.run do
    let g := fun k : UInt64 => k == seed
    return g (Id.run n) || g count
  let mut a := seed
  for i in [:count.toNat] do
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PredicateOuterBodyTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PredicateOuterBodyTest.rangePredicateOuterBodyWord, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyWord x y), true),
    (`PredicateOuterBodyTest.rangePredicateOuterBodyBoolean, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyBoolean x y), true),
    (`PredicateOuterBodyTest.rangePredicateOuterBodyUnused, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyUnused x y), true),
    (`PredicateOuterBodyTest.rangePredicateOuterBodyBound, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyBound x y), true),
    (`PredicateOuterBodyTest.rangePredicateOuterBodyInitial, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyInitial x y), true),
    (`PredicateOuterBodyTest.rangePredicateOuterBodyTail, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyTail x y), true),
    (`PredicateOuterBodyTest.rangePredicateOuterBodyCapture, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyCapture x y), true),
    (`PredicateOuterBodyTest.rangePredicateOuterBodyWrapped, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyWrapped x y), true),
    (`PredicateOuterBodyTest.rangePredicateOuterBodyNested, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyNested x y), true),
    (`PredicateOuterBodyTest.rangePredicateOuterBodyId, (fun (x y : UInt64) => PredicateOuterBodyTest.rangePredicateOuterBodyId x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: predicate outer-body extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PredicateOuterBodyTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/predicate outer-body IR comparisons passed"
