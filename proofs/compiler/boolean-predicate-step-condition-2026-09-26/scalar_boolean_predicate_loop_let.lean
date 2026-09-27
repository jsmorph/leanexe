import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateLoopLetTest

def rangeBooleanPredicateLoopLetBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == 0
    let stop := f (UInt64.ofNat i % 3 == 0)
    a := a + UInt64.ofNat i + 1
    if stop && a % 7 == 0 then break
  return a

def rangeBooleanPredicateLoopLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => !b && a != seed
    let skip := f (UInt64.ofNat i % 3 == 0)
    if skip then continue
    let kept := f (!skip) || skip
    a := a + kept.toUInt64 + UInt64.ofNat i + 1
  return a

def rangeBooleanPredicateLoopLetChoice (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b || a == seed
    let g := fun b : Bool => !b && seed != 0
    let flag := if _h : a ≤ seed then f (g false) else g (f true)
    let flag := if f flag = g false then !(g flag) else f true
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag && a % 11 == 0 then break
  return a

def rangeBooleanPredicateLoopLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : Bool → Id (Id Bool) := fun b => b && a != seed
    let flag : Id (Id Bool) := f (UInt64.ofNat i % 2 == 0)
    let _unused := f true
    let h := fun x : UInt64 => if @Eq Bool flag true then x + 3 else x + 1
    a := h a
    let flag := !(f false)
    if flag && a % 13 == 0 then break
  return a

def rangeBooleanPredicateOuterLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let flag := f (count == 0)
  let first : UInt64 := if flag then 0 else 1
  let stop := count + flag.toUInt64
  let mut a := seed + flag.toUInt64
  for i in [first.toNat:stop.toNat:2] do
    a := a + UInt64.ofNat i + 1
    if flag && a % 7 == 0 then break
  return if flag then a + 1 else a

def rangeBooleanPredicateOuterLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b && seed != 0
  let saved := !(f false)
  let h := fun x : UInt64 => if saved then x + seed else x - seed
  let saved := f (count == 0)
  let mut a := seed
  for i in [:count.toNat] do
    let flag := f (a == seed)
    a := h a + UInt64.ofNat i
    if flag && saved then break
  return if saved then a + 1 else a

def rangeBooleanPredicateOuterLetChoice (count seed : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => b || seed == 0
  let g := fun b : Bool => !b && seed != 1
  let flag := if _h : seed ≤ count then f (g false) else g (f true)
  let next := f flag != g false
  let _unused := if next then g false else f true
  let mut a := seed
  for i in [:count.toNat] do
    if next && a % 7 == 0 then continue
    a := a + UInt64.ofNat i + flag.toUInt64 + 1
  return if next then a + flag.toUInt64 else a

def rangeBooleanPredicateOuterLetId (count seed : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id Bool) := fun b => !b
  let flag : Id (Id Bool) := f (seed == 0)
  let g := fun b : Bool => (let saved := f b; Bool.toUInt64 saved) == 0
  let next := g flag
  let mut a := seed
  for i in [:count.toNat] do
    let saved := g (a == seed)
    a := a + UInt64.ofNat i + saved.toUInt64 + 1
    if next && a % 5 == 0 then break
  return if @Eq Bool flag true then a + next.toUInt64 else a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateLoopLetTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPredicateLoopLetTest.rangeBooleanPredicateLoopLetBreak, BooleanPredicateLoopLetTest.rangeBooleanPredicateLoopLetBreak, true),
    (`BooleanPredicateLoopLetTest.rangeBooleanPredicateLoopLetContinue, BooleanPredicateLoopLetTest.rangeBooleanPredicateLoopLetContinue, true),
    (`BooleanPredicateLoopLetTest.rangeBooleanPredicateLoopLetChoice, BooleanPredicateLoopLetTest.rangeBooleanPredicateLoopLetChoice, true),
    (`BooleanPredicateLoopLetTest.rangeBooleanPredicateLoopLetCapture, BooleanPredicateLoopLetTest.rangeBooleanPredicateLoopLetCapture, true),
    (`BooleanPredicateLoopLetTest.rangeBooleanPredicateOuterLetBounds, BooleanPredicateLoopLetTest.rangeBooleanPredicateOuterLetBounds, true),
    (`BooleanPredicateLoopLetTest.rangeBooleanPredicateOuterLetCapture, BooleanPredicateLoopLetTest.rangeBooleanPredicateOuterLetCapture, true),
    (`BooleanPredicateLoopLetTest.rangeBooleanPredicateOuterLetChoice, BooleanPredicateLoopLetTest.rangeBooleanPredicateOuterLetChoice, true),
    (`BooleanPredicateLoopLetTest.rangeBooleanPredicateOuterLetId, BooleanPredicateLoopLetTest.rangeBooleanPredicateOuterLetId, true)]
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
      else BooleanPredicateLoopLetTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 192 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate loop let IR comparisons passed"
