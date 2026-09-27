import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateLoopBindTest

def rangeBooleanPredicateLoopBindBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let stop ← pure (f (UInt64.ofNat i % 3 == 0))
    a := a + UInt64.ofNat i + 1
    if stop && a % 7 == 0 then break
  return a

def rangeBooleanPredicateLoopBindContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => !b || a == seed
    let skip ← Id.run (pure (!(f (UInt64.ofNat i % 3 == 0))))
    if skip then continue
    let kept ← pure (f (!skip) || skip)
    a := a + UInt64.ofNat i + kept.toUInt64 + 1
  return a

def rangeBooleanPredicateLoopBindChoice (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == seed
    let g := fun b : Bool => !b && seed != 0
    let flag ← pure (if _h : a ≤ seed then f (g false) else g (f true))
    let next ← pure (if f flag = g false then !(g flag) else f true)
    a := a + next.toUInt64 + UInt64.ofNat i
    if _h : flag then break
  return a

def rangeBooleanPredicateLoopBindCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Bool → Id Bool := fun b => b && a != seed
    let saved ← f (UInt64.ofNat i % 2 == 0)
    let _unused ← pure (Id.run (f true))
    let h := fun x : UInt64 => if saved then x + 3 else x + 1
    let saved ← pure (!(f false))
    a := h a + UInt64.ofNat i
    if saved && a % 13 == 0 then break
  return a

def rangeBooleanPredicateOuterBindBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let flag ← pure (f (count == 0))
  let first : UInt64 := if flag then 0 else 1
  let stop := count + flag.toUInt64
  let mut a := seed + flag.toUInt64
  for i in [first.toNat:stop.toNat:2] do
    a := a + UInt64.ofNat i + 1
    if flag && a % 7 == 0 then break
  return if flag then a + 1 else a

def rangeBooleanPredicateOuterBindCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved ← Id.run (pure (!(f false)))
  let h := fun x : UInt64 => if saved then x + seed else x - seed
  let saved ← pure (f (count == 0))
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (f (a == seed))
    a := h a + UInt64.ofNat i
    if flag && saved then break
  return if saved then a + 1 else a

def rangeBooleanPredicateOuterBindChoice (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let flag ← pure (if _h : seed ≤ count then f (g false) else g (f true))
  let next ← pure (f flag != g false)
  let _unused ← pure (if next then g false else f true)
  let mut a := seed
  for i in [:count.toNat] do
    if next && a % 7 == 0 then continue
    a := a + UInt64.ofNat i + flag.toUInt64 + 1
  return if next then a + flag.toUInt64 else a

def rangeBooleanPredicateOuterBindDirect (count seed : UInt64) : UInt64 := Id.run do
  let f : Bool → Id Bool := fun b => !b
  let flag ← f (seed == 0)
  let g := fun b : Bool => (Id.run do let saved ← pure (Id.run (f b)); return saved.toUInt64) == 0
  let next ← pure (g flag)
  let mut a := seed
  for i in [:count.toNat] do
    let saved ← g (a == seed)
    a := a + UInt64.ofNat i + saved.toUInt64 + 1
    if next && a % 5 == 0 then break
  return if flag then a + next.toUInt64 else a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateLoopBindTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateLoopBindTest.rangeBooleanPredicateLoopBindBreak, BooleanPredicateLoopBindTest.rangeBooleanPredicateLoopBindBreak, true),
    (`BooleanPredicateLoopBindTest.rangeBooleanPredicateLoopBindContinue, BooleanPredicateLoopBindTest.rangeBooleanPredicateLoopBindContinue, true),
    (`BooleanPredicateLoopBindTest.rangeBooleanPredicateLoopBindChoice, BooleanPredicateLoopBindTest.rangeBooleanPredicateLoopBindChoice, true),
    (`BooleanPredicateLoopBindTest.rangeBooleanPredicateLoopBindCapture, BooleanPredicateLoopBindTest.rangeBooleanPredicateLoopBindCapture, true),
    (`BooleanPredicateLoopBindTest.rangeBooleanPredicateOuterBindBounds, BooleanPredicateLoopBindTest.rangeBooleanPredicateOuterBindBounds, true),
    (`BooleanPredicateLoopBindTest.rangeBooleanPredicateOuterBindCapture, BooleanPredicateLoopBindTest.rangeBooleanPredicateOuterBindCapture, true),
    (`BooleanPredicateLoopBindTest.rangeBooleanPredicateOuterBindChoice, BooleanPredicateLoopBindTest.rangeBooleanPredicateOuterBindChoice, true),
    (`BooleanPredicateLoopBindTest.rangeBooleanPredicateOuterBindDirect, BooleanPredicateLoopBindTest.rangeBooleanPredicateOuterBindDirect, true)]
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
      else BooleanPredicateLoopBindTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate loop bind IR comparisons passed"
