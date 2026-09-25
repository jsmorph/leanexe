import LeanExe.Extract.ScalarFunc

namespace LiteralInstanceTest

def instanceDependentMany (x y : UInt64) : UInt64 :=
  let outer := x != y
  let f := fun a b c : UInt64 =>
    let inner := a == b || b == c
    if _h : outer && !inner then a + b * 3 - c else a - b * 5 + c
  f x y (x + 7)

def instanceLet (x y : UInt64) : UInt64 :=
  x + @OfNat.ofNat UInt64 (nat_lit 7) (let _unused := x + y; @UInt64.instOfNat (nat_lit 7)) - y

def instanceApplied (x y : UInt64) : UInt64 :=
  x * @OfNat.ofNat UInt64 (nat_lit 11) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 11)) (x + y)) - y

def instanceNested (x y : UInt64) : UInt64 :=
  let n := @OfNat.ofNat UInt64 (nat_lit 13)
    ((let _flag := x == y; fun (_ : UInt64) (_ : Unit) => @UInt64.instOfNat (nat_lit 13)) y ())
  n + x * y

def instanceShadow (x y : UInt64) : UInt64 :=
  let n := @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_x : UInt64) => @UInt64.instOfNat (nat_lit 5)) y)
  let f := fun x y z : UInt64 => x + n * y - z
  let n := x + y
  f y n x

def instanceProof (x y : UInt64) : UInt64 :=
  if h : x = y then x + @OfNat.ofNat UInt64 (nat_lit 17) ((fun (_ : x = y) => @UInt64.instOfNat (nat_lit 17)) h)
  else y - @OfNat.ofNat UInt64 (nat_lit 19) ((fun (_ : ¬x = y) => @UInt64.instOfNat (nat_lit 19)) h)

def instanceOverflow (x y : UInt64) : UInt64 :=
  x + @OfNat.ofNat UInt64 (nat_lit 18446744073709551621)
    ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 18446744073709551621)) y)

def instanceDo (x y : UInt64) : UInt64 := Id.run do
  let flag := x == y
  let mut a := x
  if h : flag then
    a := a + @OfNat.ofNat UInt64 (nat_lit 3) ((fun (_ : flag = true) => @UInt64.instOfNat (nat_lit 3)) h)
  else a := a - @OfNat.ofNat UInt64 (nat_lit 5) (let _unused := a; @UInt64.instOfNat (nat_lit 5))
  return a ^^^ y

def rangeInstanceStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if h : a < UInt64.ofNat i then
      a := a + @OfNat.ofNat UInt64 (nat_lit 3) ((fun (_ : a < UInt64.ofNat i) => @UInt64.instOfNat (nat_lit 3)) h)
    else a := a + @OfNat.ofNat UInt64 (nat_lit 5) (let _unused := a; @UInt64.instOfNat (nat_lit 5))
  return a

def rangeInstanceBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let increment := @OfNat.ofNat UInt64 (nat_lit 7) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 7)) a)
    a := a + increment + UInt64.ofNat i
    let stop := a % 11 == 0
    if _h : stop then break
  return a

def rangeInstanceBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := @OfNat.ofNat UInt64 (nat_lit 1) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 1)) count)
  let mut a := seed + @OfNat.ofNat UInt64 (nat_lit 13) (let _unused := count; @UInt64.instOfNat (nat_lit 13))
  for i in [first.toNat:count.toNat:2] do
    a := a + UInt64.ofNat i
    if a % 7 == 0 then continue
    a := a + @OfNat.ofNat UInt64 (nat_lit 3) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 3)) a)
  return a

def rangeInstanceOuter (count seed : UInt64) : UInt64 :=
  let f := fun x y z : UInt64 =>
    x + y * @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_ : UInt64) => @UInt64.instOfNat (nat_lit 5)) z)
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      if a % 7 == 0 then break
    return a
  f result seed count

def instanceCustom (x y : UInt64) : UInt64 :=
  x + @OfNat.ofNat UInt64 (nat_lit 5) ⟨y⟩

def instanceWrappedCustom (x y : UInt64) : UInt64 :=
  @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_ : UInt64) => ⟨y⟩) x)

def instanceWrappedVariable (x y : UInt64) : UInt64 :=
  let custom : OfNat UInt64 5 := ⟨x⟩
  @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_ : UInt64) => custom) y)

def rangeInstanceCustom (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    .yield (a + @OfNat.ofNat UInt64 (nat_lit 5) ((fun (_ : UInt64) => ⟨a⟩) seed))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end LiteralInstanceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`LiteralInstanceTest.instanceDependentMany, LiteralInstanceTest.instanceDependentMany, false),
    (`LiteralInstanceTest.instanceLet, LiteralInstanceTest.instanceLet, false),
    (`LiteralInstanceTest.instanceApplied, LiteralInstanceTest.instanceApplied, false),
    (`LiteralInstanceTest.instanceNested, LiteralInstanceTest.instanceNested, false),
    (`LiteralInstanceTest.instanceShadow, LiteralInstanceTest.instanceShadow, false),
    (`LiteralInstanceTest.instanceProof, LiteralInstanceTest.instanceProof, false),
    (`LiteralInstanceTest.instanceOverflow, LiteralInstanceTest.instanceOverflow, false),
    (`LiteralInstanceTest.instanceDo, LiteralInstanceTest.instanceDo, false),
    (`LiteralInstanceTest.rangeInstanceStep, LiteralInstanceTest.rangeInstanceStep, true),
    (`LiteralInstanceTest.rangeInstanceBreak, LiteralInstanceTest.rangeInstanceBreak, true),
    (`LiteralInstanceTest.rangeInstanceBounds, LiteralInstanceTest.rangeInstanceBounds, true),
    (`LiteralInstanceTest.rangeInstanceOuter, LiteralInstanceTest.rangeInstanceOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: literal instance extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else LiteralInstanceTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`LiteralInstanceTest.instanceCustom, `LiteralInstanceTest.instanceWrappedCustom, `LiteralInstanceTest.instanceWrappedVariable, `LiteralInstanceTest.rangeInstanceCustom] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported literal instance accepted"
  let standard (n : Nat) := Lean.Expr.app (.const ``UInt64.instOfNat []) (.lit (.natVal n))
  let numeral (evidence : Lean.Expr) := Lean.mkAppN (.const ``OfNat.ofNat [.zero])
    #[.const ``UInt64 [], .lit (.natVal 5), evidence]
  let wrapped := Lean.Expr.lam `x (.const ``UInt64 []) (standard 5) .default
  for evidence in [standard 7, wrapped, .app (standard 5) (.lit (.natVal 0)),
      .bvar 0, .app (.lam `x (.const ``UInt64 []) (standard 7) .default) (.bvar 0)] do
    unless (LeanExe.Extract.Core.extractScalarExprWith [.word (.u64 1)] (numeral evidence)).isNone do
      throwError "invalid constant-instance evidence accepted"
  let metadata := Lean.Expr.mdata {} (.app wrapped (.bvar 0))
  unless (LeanExe.Extract.Core.extractScalarExprWith [.word (.u64 1)] (numeral metadata)) == some (.u64 5) do
    throwError "metadata-wrapped standard instance rejected"
  Lean.logInfo "208 native/literal-instance IR comparisons, four declaration rejection tests, five raw instance rejection tests and one metadata test passed"
