import LeanExe.Extract.ScalarFunc

namespace CompoundGuardTest

def compoundAnd (x y : UInt64) : UInt64 :=
  if x % 2 = 1 ∧ y % 2 = 1 then 11 else 29

def compoundOr (x y : UInt64) : UInt64 :=
  if x % 2 = 1 ∨ y % 2 = 1 then 31 else 47

def compoundNested (x y : UInt64) : UInt64 :=
  if (x < y ∧ x + y ≠ 0) ∨ (x ≥ y ∧ y ≤ x * 3) then x + 13 else y - 17

def compoundNegatedLeaves (x y : UInt64) : UInt64 :=
  if (¬ x = y) ∧ (¬ x < y ∨ !(x == 0)) then ~~~x else ~~~y

def compoundZeroDivisor (x y : UInt64) : UInt64 :=
  if x = 0 ∨ (x / y = 3 ∧ y % x ≠ 0) then x / y + 1 else y % x + 7

def compoundFunction (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b : UInt64 =>
    if (a = b ∨ a < captured) ∧ (b ≠ 0 ∨ a = 0) then a + b else a - b
  f x y + f y x

def compoundDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  let z ← if x = 0 ∨ y = 0 then pure (x + y) else pure (x * y)
  if z ≥ a ∧ y ≠ 1 then a := a + z else a := a - z
  return a ^^^ y

def compoundOperand (x y : UInt64) : UInt64 :=
  if (if x < y ∧ x ≠ 0 then ~~~x else y) < (x + y) ∨ x = y
  then (if x = 0 ∧ y = 0 then 19 else x + y) else ~~~(x + y)

def rangeCompoundBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if UInt64.ofNat i ≥ seed % 5 ∧ a % 3 = 0 then break
  return a

def rangeCompoundContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if UInt64.ofNat i % 3 = 0 ∨ UInt64.ofNat i = seed % 7 then continue
    a := a + UInt64.ofNat i
  return a

def rangeCompoundJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let z ← if a = seed ∨ UInt64.ofNat i < 3 then pure (a + 5) else pure (a - 2)
    if (z > a ∧ a ≠ 0) ∨ (UInt64.ofNat i ≥ 3 ∧ seed = 0) then
      a := z
    else
      a := z + UInt64.ofNat i
    if a = 7 ∨ (a % 5 = 0 ∧ UInt64.ofNat i > 2) then break
  return a

def rangeCompoundHelper (count seed : UInt64) : UInt64 :=
  let f := fun x y : UInt64 =>
    if (x < y ∨ y = 0) ∧ (x + seed ≠ 0 ∨ y ≤ seed) then x + y + 1 else x - y
  let result := Id.run do
    let mut a := seed
    for i in [1:count.toNat:2] do
      a := f a (UInt64.ofNat i)
    return a
  f result seed

def rangeCompoundStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if (UInt64.ofNat i ≥ seed % 5 ∧ x % 3 = 0) ∨ y = 7
      then .done (x + 11) else .yield (y + UInt64.ofNat i + 1)
    finish (a + seed) a

def rangeCompoundResult (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => Id.run do
    let r : ForInStep UInt64 ←
      if (UInt64.ofNat i = seed % 7 ∨ a = 0) ∧ UInt64.ofNat i > 1
      then pure (.done (a + 3)) else pure (.yield (a + UInt64.ofNat i + 1))
    let keep : ForInStep UInt64 → ForInStep UInt64 := fun result => result
    return keep r

def compoundCustom (x y : UInt64) : UInt64 :=
  @ite UInt64 (x = y ∧ y = 0)
    (if h : x = y ∧ y = 0 then isTrue h else isFalse h) (x + 1) (y + 2)

def compoundUnsupported (x y : UInt64) : UInt64 :=
  if x = y ∨ x.toNat < y.toNat then x else y

def compoundUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => @ite UInt64 (z = y ∨ z = 0)
    (if h : z = y ∨ z = 0 then isTrue h else isFalse h) (z + 1) (y + 2)
  x + y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end CompoundGuardTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`CompoundGuardTest.compoundAnd, CompoundGuardTest.compoundAnd, false),
    (`CompoundGuardTest.compoundOr, CompoundGuardTest.compoundOr, false),
    (`CompoundGuardTest.compoundNested, CompoundGuardTest.compoundNested, false),
    (`CompoundGuardTest.compoundNegatedLeaves, CompoundGuardTest.compoundNegatedLeaves, false),
    (`CompoundGuardTest.compoundZeroDivisor, CompoundGuardTest.compoundZeroDivisor, false),
    (`CompoundGuardTest.compoundFunction, CompoundGuardTest.compoundFunction, false),
    (`CompoundGuardTest.compoundDo, CompoundGuardTest.compoundDo, false),
    (`CompoundGuardTest.compoundOperand, CompoundGuardTest.compoundOperand, false),
    (`CompoundGuardTest.rangeCompoundBreak, CompoundGuardTest.rangeCompoundBreak, true),
    (`CompoundGuardTest.rangeCompoundContinue, CompoundGuardTest.rangeCompoundContinue, true),
    (`CompoundGuardTest.rangeCompoundJoined, CompoundGuardTest.rangeCompoundJoined, true),
    (`CompoundGuardTest.rangeCompoundHelper, CompoundGuardTest.rangeCompoundHelper, true),
    (`CompoundGuardTest.rangeCompoundStep, CompoundGuardTest.rangeCompoundStep, true),
    (`CompoundGuardTest.rangeCompoundResult, CompoundGuardTest.rangeCompoundResult, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: compound guard extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else CompoundGuardTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`CompoundGuardTest.compoundCustom, `CompoundGuardTest.compoundUnsupported, `CompoundGuardTest.compoundUnusedCustom] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported compound guard accepted"
  Lean.logInfo "256 native/compound-guard IR comparisons and three rejection tests passed"
