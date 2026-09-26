import LeanExe.Extract.ScalarFunc

namespace ComplementTest

def complementDirect (x y : UInt64) : UInt64 := UInt64.complement x + y

def complementOperator (x y : UInt64) : UInt64 := ~~~(x + y)

def complementTwice (x y : UInt64) : UInt64 := ~~~(~~~x) + UInt64.complement y

def complementMixed (x y : UInt64) : UInt64 :=
  ((~~~x) &&& y) ||| ((~~~y) ^^^ (x <<< y))

def complementChoice (x y : UInt64) : UInt64 :=
  if !(~~~x == y) then ~~~(x / y) else UInt64.complement (y % x)

def complementFunction (x y : UInt64) : UInt64 :=
  let captured := ~~~(x + 7)
  let f := fun a b : UInt64 => ~~~(a * 3 + b + captured)
  f x y - f y x

def complementDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := ~~~x
  let z ← if x < y then pure (~~~(a + y)) else pure (UInt64.complement y)
  a := a ^^^ z
  return ~~~a

def complementOperand (x y : UInt64) : UInt64 :=
  if (if x == 0 then UInt64.complement y else ~~~x) ≤ (~~~y)
  then (~~~x) <<< (~~~y) else ~~~(x ^^^ y) / (~~~y)

def rangeComplement (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := ~~~(a + UInt64.ofNat i)
    if a % 5 == seed % 5 then break
  return UInt64.complement a

def rangeComplementContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (~~~(UInt64.ofNat i)) % 3 == seed % 3 then continue
    a := a ^^^ (~~~(UInt64.ofNat i + seed))
  return a

def rangeComplementHelper (count seed : UInt64) : UInt64 :=
  let f := fun x y : UInt64 => ~~~(x * 3 + y + seed)
  let result := Id.run do
    let mut a := seed
    for i in [(~~~count).toNat:(~~~count + 3).toNat:2] do
      a := f a (UInt64.ofNat i)
    return a
  f result seed

def rangeComplementStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let finish : UInt64 → UInt64 → ForInStep UInt64 := fun x y =>
      if UInt64.ofNat i == seed % 7 then .done (UInt64.complement x)
      else .yield (~~~(y + UInt64.ofNat i))
    finish (a + seed) a

def complementCustom (x y : UInt64) : UInt64 :=
  @Complement.complement UInt64 ⟨fun z => z + 1⟩ (x + y)

def complementExternal (x : UInt64) : UInt64 := ~~~x

def complementHelper (x y : UInt64) : UInt64 := complementExternal x + y

def complementUnusedCustom (x y : UInt64) : UInt64 :=
  let _f := fun z : UInt64 => @Complement.complement UInt64 ⟨fun v => v + 1⟩ z
  x + y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end ComplementTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`ComplementTest.complementDirect, ComplementTest.complementDirect, false),
    (`ComplementTest.complementOperator, ComplementTest.complementOperator, false),
    (`ComplementTest.complementTwice, ComplementTest.complementTwice, false),
    (`ComplementTest.complementMixed, ComplementTest.complementMixed, false),
    (`ComplementTest.complementChoice, ComplementTest.complementChoice, false),
    (`ComplementTest.complementFunction, ComplementTest.complementFunction, false),
    (`ComplementTest.complementDo, ComplementTest.complementDo, false),
    (`ComplementTest.complementOperand, ComplementTest.complementOperand, false),
    (`ComplementTest.rangeComplement, ComplementTest.rangeComplement, true),
    (`ComplementTest.rangeComplementContinue, ComplementTest.rangeComplementContinue, true),
    (`ComplementTest.rangeComplementHelper, ComplementTest.rangeComplementHelper, true),
    (`ComplementTest.rangeComplementStep, ComplementTest.rangeComplementStep, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: complement extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else ComplementTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`ComplementTest.complementCustom, `ComplementTest.complementHelper, `ComplementTest.complementUnusedCustom] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported complement expression accepted"
  Lean.logInfo "208 native/complement IR comparisons and three rejection tests passed"
