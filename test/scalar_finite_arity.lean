import LeanExe.Extract.ScalarFunc

namespace FiniteArityTest

def manyOrder (x y : UInt64) : UInt64 :=
  let f := fun a b c : UInt64 => (a - b) / c + a % c
  f x y (x ^^^ y)

def manyFour (x y : UInt64) : UInt64 :=
  let f := fun a b c d : UInt64 => ((a - b) <<< c) ^^^ (d >>> b)
  f x y (y + 1) (x + 7)

def manySix (x y : UInt64) : UInt64 :=
  let f := fun a b c d e g : UInt64 => a + b * 3 - c * 5 + d * 7 - e * 11 + g * 13 + x
  f x y 1 2 (x + y) (x - y)

def manyCapture (x y : UInt64) : UInt64 :=
  let captured := x + 7
  let f := fun a b c : UInt64 =>
    let g := fun d e h : UInt64 => captured + a * d - b * e + c * h
    g y x (a + b)
  let captured := y + 11
  f captured x y

def manyChained (x y : UInt64) : UInt64 :=
  let f := fun a b c : UInt64 => a + b * c
  let g := fun a b c d e : UInt64 => f (a - b) (c + d) e
  g (f x y 3) (f y x 5) x y (x ^^^ y)

def manyDo (x y : UInt64) : UInt64 := Id.run do
  let f : UInt64 → UInt64 → UInt64 → Id UInt64 := fun a b c => do
    let mut z := a + c
    if z < b then z := z + x else z := z - y
    return z ^^^ c
  let z ← f x y (x + 1)
  return f y z (y + 7)

def manyId (x y : UInt64) : UInt64 :=
  let f : UInt64 → UInt64 → UInt64 → UInt64 → Id (Id UInt64) :=
    fun a b c d => pure (pure (if a < b ∧ c != d then min a d else max b c))
  @Id.run (Id UInt64) (f x y (x + y) (x - y))

def manyUnused (x y : UInt64) : UInt64 :=
  let _f := fun a b c d e : UInt64 => (a + x) / (b - y) + c * d - e
  x ^^^ y

def rangeManyStep (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y z : UInt64 => x + y * 3 - z + UInt64.ofNat i
    let z := f a seed (UInt64.ofNat i)
    if z % 3 == 1 then continue
    a := z + 1
    if a % 7 == 0 then break
  return a

def rangeManyOuter (count seed : UInt64) : UInt64 :=
  let bound := fun a b c : UInt64 => min a b + c
  let f := fun a b c d : UInt64 => a + b * c - d
  Id.run do
    let mut a := f seed count 2 1
    for i in [:(bound count 31 0).toNat] do
      a := f a (UInt64.ofNat i) 3 seed
      if a % 7 == 0 then break
    return f a seed count 11

def rangeManyYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y z : UInt64 => x + y * z
    a := f a (UInt64.ofNat i) (seed + 1)
  return a

def rangeManyStride (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [1:count.toNat:3] do
    let f := fun x y z u v : UInt64 => x + y * z - u + v + UInt64.ofNat i
    a := f a seed 3 7 11
    if a % 5 == 0 then continue
    a := a + 1
  return a

def rangeManyGuard (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y z : UInt64 => x ^^^ (y + z)
    if f a seed (UInt64.ofNat i) < 7 ∨ (f seed a 1 == 0 ∧ True) then continue
    a := f a (UInt64.ofNat i) 3
    if a % 11 == 0 then break
  return a

def rangeManyResult (count seed : UInt64) : UInt64 :=
  let f : UInt64 → UInt64 → UInt64 → UInt64 → Id UInt64 :=
    fun a b c d => pure (a * b + c - d)
  Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i + 1
      if a % 5 == 0 then break
    return f a seed count 7

def manyUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f := fun a b c : UInt64 => UInt64.ofNat ((toString a).length) + b + c
  x + y

def manyWrongDomain (x y : UInt64) : UInt64 :=
  let _f := fun (a b c : UInt64) (d : Nat) => a + b + c + UInt64.ofNat d
  x + y

def manyIgnoredOperand (x y : UInt64) : UInt64 :=
  let f := fun (a b _c : UInt64) => a + b
  f x y (UInt64.ofNat ((toString x).length))

def manyPartial (x y : UInt64) : UInt64 :=
  let f := fun a b c : UInt64 => a + b + c
  let g := f x
  g y x

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end FiniteArityTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`FiniteArityTest.manyOrder, FiniteArityTest.manyOrder, false),
    (`FiniteArityTest.manyFour, FiniteArityTest.manyFour, false),
    (`FiniteArityTest.manySix, FiniteArityTest.manySix, false),
    (`FiniteArityTest.manyCapture, FiniteArityTest.manyCapture, false),
    (`FiniteArityTest.manyChained, FiniteArityTest.manyChained, false),
    (`FiniteArityTest.manyDo, FiniteArityTest.manyDo, false),
    (`FiniteArityTest.manyId, FiniteArityTest.manyId, false),
    (`FiniteArityTest.manyUnused, FiniteArityTest.manyUnused, false),
    (`FiniteArityTest.rangeManyStep, FiniteArityTest.rangeManyStep, true),
    (`FiniteArityTest.rangeManyOuter, FiniteArityTest.rangeManyOuter, true),
    (`FiniteArityTest.rangeManyYield, FiniteArityTest.rangeManyYield, true),
    (`FiniteArityTest.rangeManyStride, FiniteArityTest.rangeManyStride, true),
    (`FiniteArityTest.rangeManyGuard, FiniteArityTest.rangeManyGuard, true),
    (`FiniteArityTest.rangeManyResult, FiniteArityTest.rangeManyResult, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: finite-arity helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else FiniteArityTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`FiniteArityTest.manyUnusedUnsupported, `FiniteArityTest.manyWrongDomain, `FiniteArityTest.manyPartial, `FiniteArityTest.manyIgnoredOperand] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported finite-arity helper accepted"
  let operand := LeanExe.Source.Scalar.literalExpr 1
  let arguments3 := Lean.mkAppN (.bvar 0) #[operand, operand, operand]
  let arguments4 := Lean.mkAppN (.bvar 0) #[operand, operand, operand, operand]
  let acceptsAll : List LeanExe.IR.Expr → Option LeanExe.IR.Expr := fun _ => some (.u64 0)
  unless (LeanExe.Extract.Core.extractScalarExprWith [.manyFunction 4 acceptsAll] arguments3).isNone do
    throwError "three arguments accepted for a four-argument binding"
  unless (LeanExe.Extract.Core.extractScalarExprWith [.manyFunction 3 acceptsAll] arguments4).isNone do
    throwError "four arguments accepted for a three-argument binding"
  Lean.logInfo "256 native/finite-arity IR comparisons, four declaration rejection tests and two arity rejection tests passed"
