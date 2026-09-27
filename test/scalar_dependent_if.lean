import LeanExe.Extract.ScalarFunc

namespace DependentIfTest

def dependentCompare (x y : UInt64) : UInt64 :=
  if _h : x < y then x + y * 3 else x - y * 5

def dependentMixed (x y : UInt64) : UInt64 :=
  if _h : ¬ ((x == y || x == 0) ∧ (y ≤ x ∨ y != 0)) then ~~~x else ~~~y

def dependentLiteral (x y : UInt64) : UInt64 :=
  if _h : True ∧ (!false || x == y) then
    if _k : ¬False then x + y else x / y
  else y - x

def dependentNested (x y : UInt64) : UInt64 :=
  if _h : x < y then
    let z := x + y
    if _k : z ≥ y then z + x else z - x
  else if _k : x == y then x * 3 else y - x

def dependentCapture (x y : UInt64) : UInt64 :=
  let captured := x + 7
  if _h : x != y then
    let f := fun a b : UInt64 => if _k : a ≤ b then captured + a else captured - b
    let captured := y + 11
    f captured x
  else captured - y

def dependentDo (x y : UInt64) : UInt64 := Id.run do
  let mut a := x
  if _h : a < y then a := a + y else a := a - y
  let z ← if _k : a % 3 == 0 then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def dependentOperand (x y : UInt64) : UInt64 :=
  if (if _h : x ≤ y then x + 1 else y + 3) == (if _k : y == 0 then x else y)
  then (if _h : x != 0 then x / y else y % x) else ~~~(x + y)

def dependentMany (x y : UInt64) : UInt64 :=
  let f : UInt64 → UInt64 → UInt64 → Id (Id UInt64) := fun a b c =>
    pure (pure (if _h : a < b ∨ b == c then a + b * 3 - c else a - b * 5 + c))
  f x y (x + 7)

def rangeDependentYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if _h : UInt64.ofNat i % 2 = 0 then a := a + 3 else a := a + 7
  return a

def rangeDependentBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if _h : a % 7 == 0 ∨ UInt64.ofNat i ≥ 12 then break
  return a

def rangeDependentContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if _h : UInt64.ofNat i % 3 = 1 then continue
    a := a + UInt64.ofNat i
    if _h : a % 11 == 0 then break
  return a

def rangeDependentJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if _h : a < UInt64.ofNat i then a := a + 2 else a := a + 5
    let z ← if _h : a % 2 == 0 then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if _h : a % 13 == 0 then break
  return if _h : a < seed then a + count else a - count

def rangeDependentStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let f : UInt64 → UInt64 → UInt64 → ForInStep UInt64 := fun x y z =>
      if _h : x % 5 == y % 5 then
        let g := fun p q : UInt64 => if _k : p < q then p + z else q - z
        .done (g a seed)
      else .yield (x + y - z)
    f a (UInt64.ofNat i) count

def rangeDependentResult (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let result ← if _h : a % 7 == 0 then pure (ForInStep.done (a + 3))
      else pure (ForInStep.yield (a + UInt64.ofNat i))
    return result

def rangeDependentBounds (count seed : UInt64) : UInt64 := Id.run do
  let first : UInt64 := if _h : seed % 3 == 0 then 0 else 2
  let stop := if _h : count < 3 then count else count - 1
  let mut a := if _h : seed < 5 then seed + 7 else seed
  for i in [first.toNat:stop.toNat:2] do
    if _h : a % 7 == 0 then break
    a := a + UInt64.ofNat i
  return a

def rangeDependentOuter (count seed : UInt64) : UInt64 :=
  let f := fun x y z : UInt64 => if _h : x < y then x + z else y - z
  let result := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := f a (UInt64.ofNat i) count
      if _h : a == 0 then break
    return a
  if _h : result != seed then f result seed count else result

def dependentInactiveUnsupported (x y : UInt64) : UInt64 :=
  if _h : True then x else @Min.min UInt64 ⟨fun a b => a + b⟩ x y

def dependentCustomDecision (x y : UInt64) : UInt64 :=
  @dite UInt64 True (.isTrue True.intro) (fun _ => x) (fun _ => y)

def dependentUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _f := fun a b : UInt64 => if _h : False then UInt64.ofNat (toString a).length else b
  x + y

def rangeDependentInactiveUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a =>
    if _h : False then .done (UInt64.ofNat (toString a).length) else .yield (a + 1)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end DependentIfTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`DependentIfTest.dependentCompare, DependentIfTest.dependentCompare, false),
    (`DependentIfTest.dependentMixed, DependentIfTest.dependentMixed, false),
    (`DependentIfTest.dependentLiteral, DependentIfTest.dependentLiteral, false),
    (`DependentIfTest.dependentNested, DependentIfTest.dependentNested, false),
    (`DependentIfTest.dependentCapture, DependentIfTest.dependentCapture, false),
    (`DependentIfTest.dependentDo, DependentIfTest.dependentDo, false),
    (`DependentIfTest.dependentOperand, DependentIfTest.dependentOperand, false),
    (`DependentIfTest.dependentMany, DependentIfTest.dependentMany, false),
    (`DependentIfTest.rangeDependentYield, DependentIfTest.rangeDependentYield, true),
    (`DependentIfTest.rangeDependentBreak, DependentIfTest.rangeDependentBreak, true),
    (`DependentIfTest.rangeDependentContinue, DependentIfTest.rangeDependentContinue, true),
    (`DependentIfTest.rangeDependentJoined, DependentIfTest.rangeDependentJoined, true),
    (`DependentIfTest.rangeDependentStep, DependentIfTest.rangeDependentStep, true),
    (`DependentIfTest.rangeDependentResult, DependentIfTest.rangeDependentResult, true),
    (`DependentIfTest.rangeDependentBounds, DependentIfTest.rangeDependentBounds, true),
    (`DependentIfTest.rangeDependentOuter, DependentIfTest.rangeDependentOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: dependent conditional extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else DependentIfTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`DependentIfTest.dependentInactiveUnsupported, `DependentIfTest.dependentCustomDecision, `DependentIfTest.dependentUnusedUnsupported, `DependentIfTest.rangeDependentInactiveUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported dependent conditional accepted"
  let guard : LeanExe.Source.Scalar.Guard := .literal (.proposition 0 true)
  let word := LeanExe.Source.Scalar.literalExpr 1
  let step := LeanExe.Source.Scalar.Step.yieldDirect word
  let make (type body td fd : Lean.Expr) :=
    Lean.mkAppN (.const ``dite [.succ .zero]) #[type, guard.condition, guard.evidence,
      .lam `h td body .default, .lam `h fd body .default]
  let neg := Lean.Expr.app (.const ``Not []) guard.condition
  for (td, fd) in [(Lean.Expr.const ``UInt64 [], neg), (guard.condition, guard.condition)] do
    unless (LeanExe.Extract.Core.extractScalarExprWith []
        (make (.const ``UInt64 []) word td fd)).isNone do
      throwError "wrong scalar proof-lambda domain accepted"
    unless (LeanExe.Extract.Core.extractScalarStepWith []
        (make (LeanExe.Source.Scalar.Step.resultType .word) step td fd)).isNone do
      throwError "wrong step proof-lambda domain accepted"
  Lean.logInfo "304 native/dependent-if IR comparisons, four declaration rejection tests and four proof-domain rejection tests passed"
