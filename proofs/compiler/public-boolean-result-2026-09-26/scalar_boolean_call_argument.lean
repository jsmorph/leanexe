import LeanExe.Extract.ScalarFunc

namespace BooleanCallArgumentTest

def booleanCallArgumentNested (x y : UInt64) : UInt64 :=
  let f : Id (Id Bool) → Id (Id Bool) := fun (b : Id (Id Bool)) => b && x != y
  let g : Id Bool → Id UInt64 := fun (b : Id Bool) => (f b).toUInt64 + y
  Id.run (g (f (x == 0))) + Id.run (g (x != y))

def booleanCallArgumentWord (x y : UInt64) : UInt64 :=
  let p := fun n : UInt64 => n != y
  let f := fun b : Bool => !b || x == 0
  let g := fun b : Bool => if b then x + y else x - y
  g (f (p x)) + g (p (g (f true)))

def booleanCallArgumentChoice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != y
  let g := fun b : Bool => if b then x / y else x % y
  g (if f (x == 0) then f true else !(f (x != y)))

def booleanCallArgumentBind (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let g := fun b : Bool => if b then x + 3 else y + 7
  g (Id.run do
    let saved ← pure (f (x == 0))
    let word := g (f saved)
    return f (word == y))

def booleanCallArgumentCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b != (x == y)
  let g := fun b : Bool => if b then x + 1 else y - 1
  let h := fun b : Bool =>
    let saved := f b
    let f := fun other : Bool => other && saved
    g (f saved) + g (f (x == 0))
  h (f true) + h (f false)

def booleanCallArgumentDecision (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let g := fun b : Bool => if b then x + y else y - x
  g (decide (¬ f (x == 0) ∧ x < y)) + g (decide (f false ∨ y ≤ x))

def rangeBooleanCallArgumentStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Id Bool → Id Bool := fun (b : Id Bool) => b && a != 0
    let g : Id Bool → Id (ForInStep UInt64) := fun (b : Id Bool) =>
      pure (if Id.run b then .done (a + i.toUInt64) else .yield (a + 1))
    g (f (f (i.toUInt64 == seed)))

def rangeBooleanCallArgumentContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == seed
    let g := fun b : Bool => if b then a + 3 else a + i.toUInt64
    if g (f (i.toUInt64 == 0)) % 3 == 0 then
      a := g (f false)
      continue
    a := g (f (a == 0))
  return a

def rangeBooleanCallArgumentOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let g := fun b : Bool => if b then seed + 1 else seed
  let mut a := g (f (count == 0))
  for i in [:count.toNat] do
    if a < g (f (i.toUInt64 == 0)) then break
    a := a + g (f (a == seed)) + i.toUInt64
  return a + g (f false)

def rangeBooleanCallArgumentBind (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f := fun b : Bool => b || a == 0
    let g := fun b : Bool => if b then ForInStep.done (a + 3) else .yield (a + i.toUInt64 + 1)
    return g (Id.run do
      let saved ← pure (f (i.toUInt64 == seed))
      return !(f saved))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanCallArgumentTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanCallArgumentTest.booleanCallArgumentNested, BooleanCallArgumentTest.booleanCallArgumentNested, false),
    (`BooleanCallArgumentTest.booleanCallArgumentWord, BooleanCallArgumentTest.booleanCallArgumentWord, false),
    (`BooleanCallArgumentTest.booleanCallArgumentChoice, BooleanCallArgumentTest.booleanCallArgumentChoice, false),
    (`BooleanCallArgumentTest.booleanCallArgumentBind, BooleanCallArgumentTest.booleanCallArgumentBind, false),
    (`BooleanCallArgumentTest.booleanCallArgumentCapture, BooleanCallArgumentTest.booleanCallArgumentCapture, false),
    (`BooleanCallArgumentTest.booleanCallArgumentDecision, BooleanCallArgumentTest.booleanCallArgumentDecision, false),
    (`BooleanCallArgumentTest.rangeBooleanCallArgumentStep, BooleanCallArgumentTest.rangeBooleanCallArgumentStep, true),
    (`BooleanCallArgumentTest.rangeBooleanCallArgumentContinue, BooleanCallArgumentTest.rangeBooleanCallArgumentContinue, true),
    (`BooleanCallArgumentTest.rangeBooleanCallArgumentOuter, BooleanCallArgumentTest.rangeBooleanCallArgumentOuter, true),
    (`BooleanCallArgumentTest.rangeBooleanCallArgumentBind, BooleanCallArgumentTest.rangeBooleanCallArgumentBind, true)]
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
      else BooleanCallArgumentTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-call-argument IR comparisons passed"
