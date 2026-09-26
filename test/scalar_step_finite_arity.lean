import LeanExe.Extract.ScalarFunc

namespace StepFiniteArityTest

def stepManyOrder (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      if (x - y) % 7 == z % 7 then .done (x - y * 3 + z) else .yield (x + y * 5 - z)
    f a seed (UInt64.ofNat i)

def stepManyFour (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z w =>
      if x < y ∨ z == w then .done (x * 3 - y + z * 7 - w) else .yield (x - y * 5 + z + w)
    f a (UInt64.ofNat i) seed count

def stepManySix (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) :=
      fun x y z u v w => do
        let result ← pure (x + y * 3 - z * 5 + u * 7 - v * 11 + w * 13)
        if result % 5 == 0 then return .done result
        return .yield (result + 1)
    f a (UInt64.ofNat i) seed 1 2 count

def stepManyCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let captured := a + UInt64.ofNat i
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      if x % 7 == y % 7 then .done (captured + z) else .yield (captured + x - y + z)
    let captured := seed + 11
    f captured a count

def stepManyChained (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      if x % 5 == 0 then .done (x + y - z) else .yield (x - y + z)
    let g : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) :=
      fun p q r s t => pure (f (p + q) r (s + t))
    g a seed (UInt64.ofNat i) count 1

def stepManyNested (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z w =>
      let g : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun p q r =>
        if p + x < q + y then .done (p + z - w) else .yield (r + x * y - z + w)
      g a seed (UInt64.ofNat i)
    f a seed count (UInt64.ofNat i)

def stepManyBind (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y z =>
      pure (if x % 7 == y % 7 then .done (x + z) else .yield (x - y + z))
    let result ← f a seed (UInt64.ofNat i)
    let alias ← pure result
    return alias

def stepManyScalarMix (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      let g := fun p q r s : UInt64 => p + q * r - s
      let value := g x y z seed
      if value % 11 == 0 then .done value else .yield (value + UInt64.ofNat i)
    f a (UInt64.ofNat i) count

def stepManyUnused (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let _f : UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z u v =>
      if x < y then .done (a + z - u) else .yield (a + z / u + v)
    .yield (a + UInt64.ofNat i + 1)

def stepManyWrapped (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → UInt64 → Id (Id (ForInStep UInt64)) :=
      fun x y z w => pure (pure (if x % 3 == 0 then .done (x + y - z) else .yield (x - y + z + w)))
    @Id.run (Id (ForInStep UInt64)) (f a seed (UInt64.ofNat i) count)

def stepManyUnusedUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let _f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      .yield (UInt64.ofNat ((toString x).length) + y + z)
    .yield (a + 1)

def stepManyWrongDomain (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let _f : UInt64 → UInt64 → UInt64 → Bool → ForInStep UInt64 := fun x y z b =>
      if b then .done (x + y) else .yield (z + a)
    .yield (a + 1)

def stepManyPartial (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z => .yield (x + y + z)
    let g := f a
    g seed (UInt64.ofNat i)

def stepManyIgnoredOperand (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y _z => .yield (x + y)
    f a seed (UInt64.ofNat ((toString seed).length))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end StepFiniteArityTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`StepFiniteArityTest.stepManyOrder, StepFiniteArityTest.stepManyOrder, true),
    (`StepFiniteArityTest.stepManyFour, StepFiniteArityTest.stepManyFour, true),
    (`StepFiniteArityTest.stepManySix, StepFiniteArityTest.stepManySix, true),
    (`StepFiniteArityTest.stepManyCapture, StepFiniteArityTest.stepManyCapture, true),
    (`StepFiniteArityTest.stepManyChained, StepFiniteArityTest.stepManyChained, true),
    (`StepFiniteArityTest.stepManyNested, StepFiniteArityTest.stepManyNested, true),
    (`StepFiniteArityTest.stepManyBind, StepFiniteArityTest.stepManyBind, true),
    (`StepFiniteArityTest.stepManyScalarMix, StepFiniteArityTest.stepManyScalarMix, true),
    (`StepFiniteArityTest.stepManyUnused, StepFiniteArityTest.stepManyUnused, true),
    (`StepFiniteArityTest.stepManyWrapped, StepFiniteArityTest.stepManyWrapped, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: finite-arity step helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else StepFiniteArityTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`StepFiniteArityTest.stepManyUnusedUnsupported, `StepFiniteArityTest.stepManyWrongDomain, `StepFiniteArityTest.stepManyPartial, `StepFiniteArityTest.stepManyIgnoredOperand] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported finite-arity step helper accepted"
  let operand := LeanExe.Source.Scalar.literalExpr 1
  let arguments3 := Lean.mkAppN (.bvar 0) #[operand, operand, operand]
  let arguments4 := Lean.mkAppN (.bvar 0) #[operand, operand, operand, operand]
  let acceptsAll : List LeanExe.IR.Expr → Option LeanExe.Extract.Core.ScalarStepCode :=
    fun _ => some ⟨.u64 0, .u64 0⟩
  unless (LeanExe.Extract.Core.extractScalarStepWith [.manyFunction 4 acceptsAll] arguments3).isNone do
    throwError "three arguments accepted for a four-argument binding"
  unless (LeanExe.Extract.Core.extractScalarStepWith [.manyFunction 3 acceptsAll] arguments4).isNone do
    throwError "four arguments accepted for a three-argument binding"
  Lean.logInfo "240 native/step-finite-arity IR comparisons, four declaration rejection tests and two arity rejection tests passed"
