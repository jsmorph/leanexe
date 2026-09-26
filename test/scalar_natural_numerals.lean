import LeanExe.Extract.ScalarFunc

namespace NaturalNumeralTest

def naturalConverted (x y : UInt64) : UInt64 := x + UInt64.ofNat 5 - y

def naturalConvertedOverflow (x y : UInt64) : UInt64 :=
  x + UInt64.ofNat 18446744073709551621 - y

def naturalExplicitLet (x y : UInt64) : UInt64 :=
  x + @OfNat.ofNat UInt64 7 (let _unused := x + y; @UInt64.instOfNat 7) - y

def naturalExplicitApplied (x y : UInt64) : UInt64 :=
  x * @OfNat.ofNat UInt64 11 ((fun (_ : UInt64) => @UInt64.instOfNat 11) (x + y)) - y

def naturalExplicitNested (x y : UInt64) : UInt64 :=
  let n := @OfNat.ofNat UInt64 13
    ((let _flag := x == y; fun (_ : UInt64) (_ : Unit) => @UInt64.instOfNat 13) y ())
  n + x * y

def naturalDependentMany (x y : UInt64) : UInt64 :=
  let outer := x != y
  let f := fun a b c : UInt64 =>
    let inner := a == b || b == c
    if _h : outer && !inner then a + b * 3 - c else a - b * UInt64.ofNat 5 + c
  f x y (x + 7)

def naturalDo (x y : UInt64) : UInt64 := Id.run do
  let flag := x == y
  let mut a := x
  if h : flag then
    a := a + @OfNat.ofNat UInt64 3 ((fun (_ : flag = true) => @UInt64.instOfNat 3) h)
  else a := a - @OfNat.ofNat UInt64 5 (let _unused := a; @UInt64.instOfNat 5)
  return a ^^^ y

def naturalOperand (x y : UInt64) : UInt64 :=
  let flag := UInt64.ofNat 7 == x
  if _h : flag then max (UInt64.ofNat 17) y else min (UInt64.ofNat 5 + y) x

def rangeNaturalStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if h : a < UInt64.ofNat i then
      a := a + @OfNat.ofNat UInt64 3 ((fun (_ : a < UInt64.ofNat i) => @UInt64.instOfNat 3) h)
    else a := a + @OfNat.ofNat UInt64 5 (let _unused := a; @UInt64.instOfNat 5)
  return a

def rangeNaturalBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := @OfNat.ofNat UInt64 1 ((fun (_ : UInt64) => @UInt64.instOfNat 1) count)
  let mut a := seed + @OfNat.ofNat UInt64 13 (let _unused := count; @UInt64.instOfNat 13)
  for i in [first.toNat:count.toNat:2] do
    a := a + UInt64.ofNat i
    if a % 7 == 0 then continue
    a := a + @OfNat.ofNat UInt64 3 ((fun (_ : UInt64) => @UInt64.instOfNat 3) a)
  return a

def rangeNaturalConversion (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat 17 + UInt64.ofNat i
    let stop := a % 11 == 0
    if _h : stop then break
  return a

def rangeNaturalOuter (count seed : UInt64) : UInt64 :=
  let f := fun x y z : UInt64 =>
    x + y * @OfNat.ofNat UInt64 5 ((fun (_ : UInt64) => @UInt64.instOfNat 5) z)
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      if a % 7 == 0 then break
    return a
  f result seed count

def naturalCustomNat (x y : UInt64) : UInt64 :=
  x + UInt64.ofNat (@OfNat.ofNat Nat (nat_lit 5) ⟨y.toNat⟩)

def naturalCustomWord (x y : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 5 ((fun (_ : UInt64) => ⟨y⟩) x)

def naturalNotLiteral (x y : UInt64) : UInt64 :=
  UInt64.ofNat (x.toNat + y.toNat)

def rangeNaturalCustomNat (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    .yield (a + UInt64.ofNat (@OfNat.ofNat Nat (nat_lit 5) ⟨seed.toNat⟩))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end NaturalNumeralTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`NaturalNumeralTest.naturalConverted, NaturalNumeralTest.naturalConverted, false),
    (`NaturalNumeralTest.naturalConvertedOverflow, NaturalNumeralTest.naturalConvertedOverflow, false),
    (`NaturalNumeralTest.naturalExplicitLet, NaturalNumeralTest.naturalExplicitLet, false),
    (`NaturalNumeralTest.naturalExplicitApplied, NaturalNumeralTest.naturalExplicitApplied, false),
    (`NaturalNumeralTest.naturalExplicitNested, NaturalNumeralTest.naturalExplicitNested, false),
    (`NaturalNumeralTest.naturalDependentMany, NaturalNumeralTest.naturalDependentMany, false),
    (`NaturalNumeralTest.naturalDo, NaturalNumeralTest.naturalDo, false),
    (`NaturalNumeralTest.naturalOperand, NaturalNumeralTest.naturalOperand, false),
    (`NaturalNumeralTest.rangeNaturalStep, NaturalNumeralTest.rangeNaturalStep, true),
    (`NaturalNumeralTest.rangeNaturalBounds, NaturalNumeralTest.rangeNaturalBounds, true),
    (`NaturalNumeralTest.rangeNaturalConversion, NaturalNumeralTest.rangeNaturalConversion, true),
    (`NaturalNumeralTest.rangeNaturalOuter, NaturalNumeralTest.rangeNaturalOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: natural numeral extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else NaturalNumeralTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`NaturalNumeralTest.naturalCustomNat, `NaturalNumeralTest.naturalCustomWord, `NaturalNumeralTest.naturalNotLiteral, `NaturalNumeralTest.rangeNaturalCustomNat] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported natural numeral accepted"
  let natLiteral (type : Lean.Expr) (n m : Nat) := Lean.mkAppN (.const ``OfNat.ofNat [.zero])
    #[type, .lit (.natVal n), .app (.const ``instOfNatNat []) (.lit (.natVal m))]
  let convert (value : Lean.Expr) := Lean.Expr.app (.const ``UInt64.ofNat []) value
  let natType := Lean.Expr.const ``Nat []
  let good := natLiteral natType 5 5
  for value in [natLiteral (.const ``Bool []) 5 5, natLiteral natType 5 7,
      .app (.app (.app (.const ``OfNat.ofNat [.zero]) natType) (.lit (.natVal 5))) (.bvar 0),
      natLiteral (.mdata {} (.const ``UInt64 [])) 5 5] do
    unless (LeanExe.Extract.Core.extractScalarExprWith [] (convert value)).isNone do
      throwError "invalid natural numeral accepted"
  let mismatched := Lean.mkAppN (.const ``OfNat.ofNat [.zero])
    #[.const ``UInt64 [], good, .app (.const ``UInt64.instOfNat []) (natLiteral natType 7 7)]
  unless (LeanExe.Extract.Core.extractScalarExprWith [] mismatched).isNone do
    throwError "mismatched explicit UInt64 numeral and instance accepted"
  let decorated := Lean.Expr.mdata {} (natLiteral (.mdata {} (.mdata {} natType)) 5 5)
  unless (LeanExe.Extract.Core.extractScalarExprWith [] (convert decorated)) == some (.u64 5) do
    throwError "metadata-decorated Nat conversion rejected"
  let explicit := Lean.mkAppN (.const ``OfNat.ofNat [.zero])
    #[.const ``UInt64 [], decorated, .app (.const ``UInt64.instOfNat []) decorated]
  unless (LeanExe.Extract.Core.extractScalarExprWith [] explicit) == some (.u64 5) do
    throwError "metadata-decorated explicit numeral rejected"
  Lean.logInfo "208 native/natural-numeral IR comparisons, four declaration rejection tests, five raw numeral rejection tests and two metadata tests passed"
