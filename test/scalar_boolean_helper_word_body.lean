import LeanExe.Extract.ScalarFunc

namespace PredicateBodyWordTest

def predicateBodyWordRepeated (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0)
  (f x).toUInt64 + (f y).toUInt64 + x

def predicateBodyWordBoolean (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => (let g := fun n : UInt64 => n == y || b; g x && g 0)
  if f (x == 0) then x + 7 else y * 3

def predicateBodyWordUnused (x y : UInt64) : UInt64 :=
  let _unused := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0)
  x + y

def predicateBodyWordCapture (x y : UInt64) : UInt64 :=
  let p := fun n : UInt64 => n == y
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g x && g 0)
  if _h : f (x == 0) ≠ f (y == 0) then x + 3 else y + 11

def predicateBodyWordProposition (x y : UInt64) : UInt64 :=
  if x < y ∧ (let f := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0); f x && f y) then x + 7 else y + 3

def predicateBodyWordDo (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => Id.run do
    let g := fun k : Bool => k || x == y
    return g b && g (y == 0)
  if _h : f (x == 0) then x + y else x - y

def rangePredicateBodyWordStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g a); (f a).toUInt64 + (f i.toUInt64).toUInt64) = 1 then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangePredicateBodyWordExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g a && g seed); (f (i.toUInt64 == 0)).toUInt64) = 1 then break
  return a

def rangePredicateBodyWordContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0)); f a || f i.toUInt64) ∧ a ≤ seed then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangePredicateBodyWordTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (let f := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g a && g 0); (f (a == 0)).toUInt64 + (f (a == seed)).toUInt64) + a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PredicateBodyWordTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PredicateBodyWordTest.predicateBodyWordRepeated, (fun (x y : UInt64) => PredicateBodyWordTest.predicateBodyWordRepeated x y), false),
    (`PredicateBodyWordTest.predicateBodyWordBoolean, (fun (x y : UInt64) => PredicateBodyWordTest.predicateBodyWordBoolean x y), false),
    (`PredicateBodyWordTest.predicateBodyWordUnused, (fun (x y : UInt64) => PredicateBodyWordTest.predicateBodyWordUnused x y), false),
    (`PredicateBodyWordTest.predicateBodyWordCapture, (fun (x y : UInt64) => PredicateBodyWordTest.predicateBodyWordCapture x y), false),
    (`PredicateBodyWordTest.predicateBodyWordProposition, (fun (x y : UInt64) => PredicateBodyWordTest.predicateBodyWordProposition x y), false),
    (`PredicateBodyWordTest.predicateBodyWordDo, (fun (x y : UInt64) => PredicateBodyWordTest.predicateBodyWordDo x y), false),
    (`PredicateBodyWordTest.rangePredicateBodyWordStep, (fun (x y : UInt64) => PredicateBodyWordTest.rangePredicateBodyWordStep x y), true),
    (`PredicateBodyWordTest.rangePredicateBodyWordExit, (fun (x y : UInt64) => PredicateBodyWordTest.rangePredicateBodyWordExit x y), true),
    (`PredicateBodyWordTest.rangePredicateBodyWordContinue, (fun (x y : UInt64) => PredicateBodyWordTest.rangePredicateBodyWordContinue x y), true),
    (`PredicateBodyWordTest.rangePredicateBodyWordTail, (fun (x y : UInt64) => PredicateBodyWordTest.rangePredicateBodyWordTail x y), true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: predicate word-body extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PredicateBodyWordTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/predicate word-body IR comparisons passed"
