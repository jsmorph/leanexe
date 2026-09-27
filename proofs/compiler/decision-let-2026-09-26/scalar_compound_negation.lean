import LeanExe.Extract.ScalarFunc

namespace CompoundNegationTest

def compoundNotAnd (x y : UInt64) : UInt64 :=
  if ¬ (x % 2 = 1 ∧ y % 2 = 1) then 11 else 29

def compoundNotOr (x y : UInt64) : UInt64 :=
  if ¬ (x % 2 = 1 ∨ y % 2 = 1) then 31 else 47

def compoundNotTwice (x y : UInt64) : UInt64 :=
  if ¬ ¬ (x < y ∧ x + y ≠ 0) then x + 13 else y - 17

def compoundNotThrice (x y : UInt64) : UInt64 :=
  if ¬ ¬ ¬ (x ≥ y ∨ y ≤ x * 3) then ~~~x else ~~~y

def compoundNotNested (x y : UInt64) : UInt64 :=
  if ¬ ((¬ (x = 0 ∨ y = 0)) ∧ (x / y = 3 ∨ ¬ (y % x = 0 ∧ x ≠ y)))
  then x / y + 1 else y % x + 7

def compoundNotFunction (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b : UInt64 =>
    if (¬ (a = b ∨ a < captured)) ∨ (¬ (b ≠ 0 ∧ a = 0)) then a + b else a - b
  f x y + f y x

def compoundNotDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  let z ← if ¬ (x = 0 ∨ y = 0) then pure (x + y) else pure (x * y)
  if ¬ ¬ (z ≥ a ∧ y ≠ 1) then a := a + z else a := a - z
  return a ^^^ y

def compoundNotOperand (x y : UInt64) : UInt64 :=
  if (if ¬ (x < y ∧ x ≠ 0) then ~~~x else y) < (x + y) ∧ ¬ (x = y ∨ x = 0)
  then (if ¬ (x = 0 ∧ y = 0) then 19 else x + y) else ~~~(x + y)

def rangeCompoundNotBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if ¬ (UInt64.ofNat i < seed % 5 ∨ a % 3 ≠ 0) then break
  return a

def rangeCompoundNotContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if ¬ ¬ (UInt64.ofNat i % 3 = 0 ∨ ¬ (UInt64.ofNat i ≠ seed % 7 ∧ a ≠ 0)) then continue
    a := a + UInt64.ofNat i
  return a

def rangeCompoundNotJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let z ← if ¬ (a = seed ∧ UInt64.ofNat i < 3) then pure (a + 5) else pure (a - 2)
    if (¬ (z > a ∧ a ≠ 0)) ∨ (¬ (UInt64.ofNat i ≥ 3 ∨ seed = 0)) then
      a := z
    else
      a := z + UInt64.ofNat i
    if ¬ (a ≠ 7 ∧ ¬ (a % 5 = 0 ∧ UInt64.ofNat i > 2)) then break
  return a

def rangeCompoundNotStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => Id.run do
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if ¬ ¬ ¬ ((UInt64.ofNat i ≥ seed % 5 ∧ x % 3 = 0) ∨ y = 7)
      then .done (x + 11) else .yield (y + UInt64.ofNat i + 1)
    let r : ForInStep UInt64 ← pure (finish (a + seed) a)
    let keep : ForInStep UInt64 → ForInStep UInt64 := fun result => result
    return keep r

def compoundNotCustom (x y : UInt64) : UInt64 :=
  @ite UInt64 (¬ (x = y ∧ y = 0))
    (if h : ¬ (x = y ∧ y = 0) then isTrue h else isFalse h) (x + 1) (y + 2)

def compoundNotInnerCustom (x y : UInt64) : UInt64 :=
  @ite UInt64 (¬ (x = y ∧ y = 0))
    (@instDecidableNot (x = y ∧ y = 0)
      (if h : x = y ∧ y = 0 then isTrue h else isFalse h)) x y

def compoundNotUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => @ite UInt64 (¬ (z = y ∨ z = 0))
    (if h : ¬ (z = y ∨ z = 0) then isTrue h else isFalse h) (z + 1) (y + 2)
  x + y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end CompoundNegationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`CompoundNegationTest.compoundNotAnd, CompoundNegationTest.compoundNotAnd, false),
    (`CompoundNegationTest.compoundNotOr, CompoundNegationTest.compoundNotOr, false),
    (`CompoundNegationTest.compoundNotTwice, CompoundNegationTest.compoundNotTwice, false),
    (`CompoundNegationTest.compoundNotThrice, CompoundNegationTest.compoundNotThrice, false),
    (`CompoundNegationTest.compoundNotNested, CompoundNegationTest.compoundNotNested, false),
    (`CompoundNegationTest.compoundNotFunction, CompoundNegationTest.compoundNotFunction, false),
    (`CompoundNegationTest.compoundNotDo, CompoundNegationTest.compoundNotDo, false),
    (`CompoundNegationTest.compoundNotOperand, CompoundNegationTest.compoundNotOperand, false),
    (`CompoundNegationTest.rangeCompoundNotBreak, CompoundNegationTest.rangeCompoundNotBreak, true),
    (`CompoundNegationTest.rangeCompoundNotContinue, CompoundNegationTest.rangeCompoundNotContinue, true),
    (`CompoundNegationTest.rangeCompoundNotJoined, CompoundNegationTest.rangeCompoundNotJoined, true),
    (`CompoundNegationTest.rangeCompoundNotStep, CompoundNegationTest.rangeCompoundNotStep, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: compound negation extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else CompoundNegationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`CompoundNegationTest.compoundNotCustom, `CompoundNegationTest.compoundNotInnerCustom, `CompoundNegationTest.compoundNotUnusedCustom] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported compound negation accepted"
  Lean.logInfo "208 native/compound-negation IR comparisons and three rejection tests passed"
