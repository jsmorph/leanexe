import LeanExe.Extract.ScalarFunc

namespace LiteralGuardTest

def literalBoolTrue (x y : UInt64) : UInt64 := if true then x + 3 else y - 1

def literalBoolFalse (x y : UInt64) : UInt64 := if false then x / y else y % x

def literalPropTrue (x y : UInt64) : UInt64 := if True then x ^^^ y else x * y

def literalPropFalse (x y : UInt64) : UInt64 := if False then min x y else max x y

def literalNegations (x y : UInt64) : UInt64 :=
  if !(!(!false)) then
    if ¬¬True then x + y else ~~~x
  else if ¬(!(!true) : Bool) then y else x - y

def literalCompound (x y : UInt64) : UInt64 :=
  if ((true && (x == y || false)) ∧ (False ∨ x ≤ y)) ∨
      ((¬True) ∧ (!false || y == 0))
  then x + 7 else y - 3

def literalFunction (x y : UInt64) : UInt64 :=
  let bias := x + 7
  let f := fun a b : UInt64 =>
    if true && (a == b || !false) then a + bias else if False then b else b - bias
  f x y + f y x

def literalDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  if True then a := a + y else a := a - y
  let z ← if false then pure (a * y) else pure (a ^^^ y)
  if ¬False ∧ (true || x == y) then a := a + z
  return a

def rangeLiteralBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if true then break
    a := a + 99
  return a

def rangeLiteralContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if false then continue
    if True ∧ UInt64.ofNat i % 3 = 1 then continue
    a := a + UInt64.ofNat i
    if False then break
  return a

def rangeLiteralJoined (count seed : UInt64) : UInt64 :=
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      let z ← if !(false || UInt64.ofNat i % 2 == 0) then pure (a + 1) else pure (a + 3)
      a := z
      if ¬False ∧ (true && a % 7 == 0) then break
    return a
  if true then result + seed else result - count

def rangeLiteralStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if (False ∨ x = seed) ∨ (¬¬True ∧ (!(!true) && y % 5 == 0))
      then .done (max x y) else .yield (min (x + UInt64.ofNat i) (y + 3))
    finish (a + 1) (a + seed)

def literalInactiveUnsupported (x y : UInt64) : UInt64 :=
  if true then x else @Min.min UInt64 ⟨fun a b => a + b⟩ x y

def literalCustomDecision (x y : UInt64) : UInt64 :=
  @ite UInt64 True (.isTrue True.intro) x y

def literalUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 =>
    if False then @Min.min UInt64 ⟨fun a b => a ^^^ b⟩ z y else z
  if true then x else y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end LiteralGuardTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`LiteralGuardTest.literalBoolTrue, LiteralGuardTest.literalBoolTrue, false),
    (`LiteralGuardTest.literalBoolFalse, LiteralGuardTest.literalBoolFalse, false),
    (`LiteralGuardTest.literalPropTrue, LiteralGuardTest.literalPropTrue, false),
    (`LiteralGuardTest.literalPropFalse, LiteralGuardTest.literalPropFalse, false),
    (`LiteralGuardTest.literalNegations, LiteralGuardTest.literalNegations, false),
    (`LiteralGuardTest.literalCompound, LiteralGuardTest.literalCompound, false),
    (`LiteralGuardTest.literalFunction, LiteralGuardTest.literalFunction, false),
    (`LiteralGuardTest.literalDo, LiteralGuardTest.literalDo, false),
    (`LiteralGuardTest.rangeLiteralBreak, LiteralGuardTest.rangeLiteralBreak, true),
    (`LiteralGuardTest.rangeLiteralContinue, LiteralGuardTest.rangeLiteralContinue, true),
    (`LiteralGuardTest.rangeLiteralJoined, LiteralGuardTest.rangeLiteralJoined, true),
    (`LiteralGuardTest.rangeLiteralStep, LiteralGuardTest.rangeLiteralStep, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: literal guard extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else LiteralGuardTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`LiteralGuardTest.literalInactiveUnsupported, `LiteralGuardTest.literalCustomDecision, `LiteralGuardTest.literalUnusedUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported literal guard accepted"
  Lean.logInfo "208 native/literal-guard IR comparisons and three rejection tests passed"
