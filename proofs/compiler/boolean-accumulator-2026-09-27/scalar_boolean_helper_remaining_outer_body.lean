import LeanExe.Extract.ScalarFunc

namespace PredicateRemainingOuterTest

def rangePredicateOuterWordFromBoolean (count seed : UInt64) : UInt64 :=
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (count == 0) && g (n % 3 == 0))
  let flag := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f a then break
      a := a + i.toUInt64 + 1
    return f a
  if flag then seed + count else seed * 3

def rangePredicateOuterBooleanFromBoolean (count seed : UInt64) : UInt64 :=
  let f := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g count && g 0)
  let flag := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f (a == 0) then break
      a := a + i.toUInt64 + 1
    return f (a == seed)
  if flag then seed + count else seed * 3

def rangePredicateOuterWordConditional (count seed : UInt64) : UInt64 :=
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (count == 0) && g (n % 3 == 0))
  if f seed then
    let flag := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if f a then break
        a := a + i.toUInt64 + 1
      return f a
    if flag then seed + count else seed * 3
  else count + seed

def rangePredicateOuterBooleanConditional (count seed : UInt64) : UInt64 :=
  let f := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g count && g 0)
  if f (seed == 0) then
    let flag := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if f (a == 0) then break
        a := a + i.toUInt64 + 1
      return f (a == seed)
    if flag then seed + count else seed * 3
  else count + seed

def rangePredicateOuterDerivedUnused (count seed : UInt64) : UInt64 :=
  let _unused := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g count && g 0)
  let flag := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a == seed
  if flag then seed + count else seed * 3

def rangePredicateOuterDerivedWrapped (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => Id.run do
    let g := fun n : UInt64 => n == seed || b
    return g count && g 0
  let flag ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if f (a == 0) then break
      a := a + i.toUInt64 + 1
    return f (a == seed))
  return if flag then seed + count else seed * 3

def rangePredicateOuterChoiceCapture (count seed : UInt64) : UInt64 :=
  let p := fun n : UInt64 => n % 5 == 0
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g count && g seed)
  if f (seed == 0) then
    let flag := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if f (i.toUInt64 == 0) then continue
        a := a + i.toUInt64 + 1
        if f (a == seed) then break
      return f (a == seed)
    if flag then seed + count else seed * 3
  else count + seed

def rangePredicateOuterChoiceNested (count seed : UInt64) : Id UInt64 := do
  let f := fun n : Id UInt64 => Id.run do
    let g := fun b : Bool => (let h := fun k : UInt64 => k == Id.run n || b; h count && h seed)
    return g (Id.run n % 3 == 0) || g (seed == 0)
  if f seed then
    let flag ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if f a then break
        a := a + i.toUInt64 + 1
      return f a)
    return if flag then seed + count else seed * 3
  else return count + seed

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PredicateRemainingOuterTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PredicateRemainingOuterTest.rangePredicateOuterWordFromBoolean, (fun (x y : UInt64) => PredicateRemainingOuterTest.rangePredicateOuterWordFromBoolean x y), true),
    (`PredicateRemainingOuterTest.rangePredicateOuterBooleanFromBoolean, (fun (x y : UInt64) => PredicateRemainingOuterTest.rangePredicateOuterBooleanFromBoolean x y), true),
    (`PredicateRemainingOuterTest.rangePredicateOuterWordConditional, (fun (x y : UInt64) => PredicateRemainingOuterTest.rangePredicateOuterWordConditional x y), true),
    (`PredicateRemainingOuterTest.rangePredicateOuterBooleanConditional, (fun (x y : UInt64) => PredicateRemainingOuterTest.rangePredicateOuterBooleanConditional x y), true),
    (`PredicateRemainingOuterTest.rangePredicateOuterDerivedUnused, (fun (x y : UInt64) => PredicateRemainingOuterTest.rangePredicateOuterDerivedUnused x y), true),
    (`PredicateRemainingOuterTest.rangePredicateOuterDerivedWrapped, (fun (x y : UInt64) => PredicateRemainingOuterTest.rangePredicateOuterDerivedWrapped x y), true),
    (`PredicateRemainingOuterTest.rangePredicateOuterChoiceCapture, (fun (x y : UInt64) => PredicateRemainingOuterTest.rangePredicateOuterChoiceCapture x y), true),
    (`PredicateRemainingOuterTest.rangePredicateOuterChoiceNested, (fun (x y : UInt64) => PredicateRemainingOuterTest.rangePredicateOuterChoiceNested x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: remaining outer predicate body extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PredicateRemainingOuterTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/remaining outer predicate body IR comparisons passed"
