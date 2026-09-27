import LeanExe.Extract.ScalarFunc

namespace NatToUInt64Test

def natAliasLiteral (x y : UInt64) : UInt64 := x + (5 : Nat).toUInt64 - y

def natAliasOverflow (x y : UInt64) : UInt64 :=
  x + (18446744073709551621 : Nat).toUInt64 - y

def natAliasChoice (x y : UInt64) : UInt64 :=
  if x < (7 : Nat).toUInt64 then y + (19 : Nat).toUInt64 else x - (3 : Nat).toUInt64

def natAliasHelper (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => n + (18446744073709551616 : Nat).toUInt64
  f x + f y

def natAliasDo (x y : UInt64) : UInt64 := Id.run do
  let a ← pure (x + (11 : Nat).toUInt64)
  let b ← pure (y + (13 : Nat).toUInt64)
  return a ^^^ b

def natAliasPredicate (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b && x != (3 : Nat).toUInt64
  let g := fun n : UInt64 => f (n == (7 : Nat).toUInt64)
  (g y).toUInt64 + x

def rangeNatAliasStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + (7 : Nat).toUInt64
  return a

def rangeNatAliasCondition (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:2] do
    if _h : i.toUInt64 == a then
      a := a + (5 : Nat).toUInt64
      break
    a := a + i.toUInt64
    if a % (3 : Nat).toUInt64 == 0 then continue
    a := a + 1
  return a

def rangeNatAliasCapture (count seed : UInt64) : UInt64 := Id.run do
  let f := fun n : UInt64 => n + (5 : Nat).toUInt64
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun n : UInt64 => f n + i.toUInt64
    a := g a
  return f a

def rangeNatAliasPredicateResult (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => b && a != seed
    let g := fun b : Bool => !(f b)
    if g (i.toUInt64 < seed) then
      a := a + 7
      break
    a := a + i.toUInt64 + 1
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end NatToUInt64Test

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`NatToUInt64Test.natAliasLiteral, NatToUInt64Test.natAliasLiteral, false),
    (`NatToUInt64Test.natAliasOverflow, NatToUInt64Test.natAliasOverflow, false),
    (`NatToUInt64Test.natAliasChoice, NatToUInt64Test.natAliasChoice, false),
    (`NatToUInt64Test.natAliasHelper, NatToUInt64Test.natAliasHelper, false),
    (`NatToUInt64Test.natAliasDo, NatToUInt64Test.natAliasDo, false),
    (`NatToUInt64Test.natAliasPredicate, NatToUInt64Test.natAliasPredicate, false),
    (`NatToUInt64Test.rangeNatAliasStep, NatToUInt64Test.rangeNatAliasStep, true),
    (`NatToUInt64Test.rangeNatAliasCondition, NatToUInt64Test.rangeNatAliasCondition, true),
    (`NatToUInt64Test.rangeNatAliasCapture, NatToUInt64Test.rangeNatAliasCapture, true),
    (`NatToUInt64Test.rangeNatAliasPredicateResult, NatToUInt64Test.rangeNatAliasPredicateResult, true)]
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
      else NatToUInt64Test.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 180 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Nat.toUInt64 IR comparisons passed"
