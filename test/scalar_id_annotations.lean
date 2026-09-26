import LeanExe.Extract.ScalarFunc

namespace IdAnnotationTest

def idReturnedHelper (x y : UInt64) : UInt64 := Id.run do
  let f : PUnit.{1} → UInt64 → Id UInt64 := fun _ a => do
    let mut z := a
    if z < x then z := z + y else z := z - y
    return z ^^^ x
  let z ← f PUnit.unit y
  return f PUnit.unit (z + x)

def idPureNested (x y : UInt64) : UInt64 :=
  @Id.run (Id (Id UInt64))
    (@Pure.pure Id _ (Id (Id UInt64)) (@Pure.pure Id _ (Id UInt64) (pure (x + y))))

def idRunNested (x y : UInt64) : UInt64 :=
  @Id.run (Id UInt64) (@Id.run (Id (Id UInt64)) (pure (pure (pure (x - y)))))

def idBindInput (x y : UInt64) : UInt64 :=
  @Bind.bind Id (@Monad.toBind Id Id.instMonad) (Id UInt64) (Id (Id UInt64))
    (pure (pure (x + y))) (fun value =>
      @Pure.pure Id _ (Id (Id UInt64)) (pure (pure (UInt64.mul value x))))

def idBindOutput (x y : UInt64) : UInt64 := Id.run do
  let f : UInt64 → Id (Id UInt64) := fun a => pure (pure (a + x))
  let z ← pure (x ^^^ y)
  return f (y + z)

def idConditional (x y : UInt64) : UInt64 :=
  @Id.run (Id UInt64) (if x < y then pure (pure (x + 7)) else pure (pure (y - 3)))

def idFunctions (x y : UInt64) : UInt64 :=
  let f : UInt64 → UInt64 → Id (Id UInt64) := fun a b => pure (pure (min (a + x) (b + y)))
  let g : PUnit.{1} → UInt64 → Id (Id UInt64) := fun _ a => f a y
  @Id.run (Id UInt64) (g PUnit.unit (x + y))

def idUnused (x y : UInt64) : UInt64 :=
  let _f : UInt64 → Id (Id UInt64) := fun a => pure (pure (a * x))
  y + 1

def rangeIdWrapped (count seed : UInt64) : UInt64 :=
  @Id.run (Id UInt64) (@Pure.pure Id _ (Id UInt64) (Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i + 1
    return a))

def rangeIdBindLeft (count seed : UInt64) : UInt64 :=
  @Bind.bind Id (@Monad.toBind Id Id.instMonad) UInt64 (Id UInt64)
    (Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        a := a + UInt64.ofNat i + 1
        if a % 5 == 0 then break
      return a)
    (fun result => @Pure.pure Id _ (Id UInt64) (pure (result + seed)))

def rangeIdBindRight (count seed : UInt64) : UInt64 :=
  @Bind.bind Id (@Monad.toBind Id Id.instMonad) (Id UInt64) UInt64
    (pure (pure (seed + 1))) (fun initial => Id.run do
      let mut a : UInt64 := initial
      for i in [:count.toNat] do
        a := a + UInt64.ofNat i
      return a)

def rangeIdStepHelper (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let f : UInt64 → Id (Id UInt64) := fun x => pure (pure (x + UInt64.ofNat i))
    let z : UInt64 := @Id.run (Id UInt64) (f a)
    if z % 3 == 1 then continue
    a := z + 1
    if a % 5 == 0 then break
  return a

def idCustomPure (x y : UInt64) : UInt64 :=
  @Pure.pure Id ⟨fun value => value⟩ (Id UInt64) (pure (x + y))

def idCustomBind (x y : UInt64) : UInt64 :=
  @Bind.bind Id ⟨fun value next => next value⟩ UInt64 (Id UInt64)
    x (fun value => pure (pure (value + y)))

def idUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f : UInt64 → Id (Id UInt64) := fun a =>
    pure (pure (@Min.min UInt64 ⟨fun b c => b ^^^ c⟩ a y))
  x + y

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end IdAnnotationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`IdAnnotationTest.idReturnedHelper, IdAnnotationTest.idReturnedHelper, false),
    (`IdAnnotationTest.idPureNested, IdAnnotationTest.idPureNested, false),
    (`IdAnnotationTest.idRunNested, IdAnnotationTest.idRunNested, false),
    (`IdAnnotationTest.idBindInput, IdAnnotationTest.idBindInput, false),
    (`IdAnnotationTest.idBindOutput, IdAnnotationTest.idBindOutput, false),
    (`IdAnnotationTest.idConditional, IdAnnotationTest.idConditional, false),
    (`IdAnnotationTest.idFunctions, IdAnnotationTest.idFunctions, false),
    (`IdAnnotationTest.idUnused, IdAnnotationTest.idUnused, false),
    (`IdAnnotationTest.rangeIdWrapped, IdAnnotationTest.rangeIdWrapped, true),
    (`IdAnnotationTest.rangeIdBindLeft, IdAnnotationTest.rangeIdBindLeft, true),
    (`IdAnnotationTest.rangeIdBindRight, IdAnnotationTest.rangeIdBindRight, true),
    (`IdAnnotationTest.rangeIdStepHelper, IdAnnotationTest.rangeIdStepHelper, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Id annotation extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else IdAnnotationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`IdAnnotationTest.idCustomPure, `IdAnnotationTest.idCustomBind, `IdAnnotationTest.idUnusedUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Id annotation accepted"
  Lean.logInfo "208 native/Id-annotation IR comparisons and three rejection tests passed"
