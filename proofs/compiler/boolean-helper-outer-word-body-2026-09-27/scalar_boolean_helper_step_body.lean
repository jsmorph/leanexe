import LeanExe.Extract.ScalarFunc

namespace PredicateStepBodyTest

def rangePredicateBodyBreakWord (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 7 == 0; g n || g seed)
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyBreakBoolean (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g a && g seed)
    if f (i.toUInt64 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyContinueWord (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0))
    if f a || f i.toUInt64 then continue
    a := a * 3 + i.toUInt64 + 1
    if f a then break
  return a

def rangePredicateBodyContinueBoolean (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => n % 3 == 0 || b; g a && g seed)
    if f (i.toUInt64 == 0) then continue
    a := a * 3 + i.toUInt64 + 1
    if f (a == seed) then break
  return a

def rangePredicateBodyDependent (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (if _h : n < seed then (let g := fun k : UInt64 => k % 3 == 0; g n || g a) else n == a)
    if _h : f a ≠ f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyCapture (count seed : UInt64) : Id UInt64 := do
  let p := fun n : UInt64 => n % 5 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g a && g seed)
    a := a + i.toUInt64 + 1
    if f (a == seed) then break
  return a

def rangePredicateBodyUnused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := fun b : Bool => (let g := fun n : UInt64 => n % 3 == 0 || b; g a && g seed)
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a

def rangePredicateBodyWrapped (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => Id.run do
      let g := fun k : Bool => k || a == seed
      return g b && g (i.toUInt64 == 0)
    if _h : f (a % 3 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyNested (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun b : Bool => (let h := fun k : UInt64 => k == n || b; h a && h seed); g (n % 3 == 0) || g (i.toUInt64 == 0))
    if f a then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyId (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : Id UInt64 => Id.run do
      let g := fun k : UInt64 => k == seed
      return g (Id.run n) || g a
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PredicateStepBodyTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PredicateStepBodyTest.rangePredicateBodyBreakWord, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyBreakWord x y), true),
    (`PredicateStepBodyTest.rangePredicateBodyBreakBoolean, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyBreakBoolean x y), true),
    (`PredicateStepBodyTest.rangePredicateBodyContinueWord, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyContinueWord x y), true),
    (`PredicateStepBodyTest.rangePredicateBodyContinueBoolean, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyContinueBoolean x y), true),
    (`PredicateStepBodyTest.rangePredicateBodyDependent, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyDependent x y), true),
    (`PredicateStepBodyTest.rangePredicateBodyCapture, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyCapture x y), true),
    (`PredicateStepBodyTest.rangePredicateBodyUnused, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyUnused x y), true),
    (`PredicateStepBodyTest.rangePredicateBodyWrapped, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyWrapped x y), true),
    (`PredicateStepBodyTest.rangePredicateBodyNested, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyNested x y), true),
    (`PredicateStepBodyTest.rangePredicateBodyId, (fun (x y : UInt64) => PredicateStepBodyTest.rangePredicateBodyId x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: predicate step-body extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PredicateStepBodyTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 240 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/predicate step-body IR comparisons passed"
