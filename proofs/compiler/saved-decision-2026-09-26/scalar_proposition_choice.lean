import LeanExe.Extract.ScalarFunc

namespace PropositionChoiceTest

def propChoiceLet (x y : UInt64) : UInt64 :=
  let a := if x = y then true else false
  let b := if x ≠ y then true else false
  let c := if x < y then x != 0 else y == 0
  let d := if x ≤ y then a else b
  let e := if x > y then c else d
  let f := if x ≥ y then e else !c
  if (a || b) && f then x + y * 3 else x - y * 5

def propChoiceNested (x y : UInt64) : UInt64 :=
  let flag := x == y
  let result := !!!(if (if x ≤ y then (if flag then x == 0 else y == 0) else x != 0) then
    (if !flag then x != 0 else false) else (if flag then true else y != 0))
  if result then ~~~x else ~~~y

def propChoiceClosed (x y : UInt64) : UInt64 :=
  if (if x < y ∧ y ≠ 0 then x != 0 else y == 0) then x + 7 else y - 11

def propChoiceShadow (x y : UInt64) : UInt64 :=
  let flag := if x = y then true else x == 0
  let f := fun a b : UInt64 => if (if flag then a != b else b == 0) then a + b else a - b
  let flag := if y ≠ 0 then false else !flag
  if flag then f x y else f y x

def propChoiceCapture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun a b c : UInt64 =>
    let inner := if (a < b ∨ b ≥ c) ∧ ¬ (a = c) then outer || a == b else !outer && a != c
    if inner then a + b * 3 - c else a - b + c
  f x y (x + 7)

def propChoiceDependent (x y : UInt64) : UInt64 :=
  let flag := x == y
  if _h : (if x < y then flag else !flag) then
    let next := if x ≤ y then flag && y == 0 else x != 0
    if next then y + 3 else x - 5
  else
    let next := if ¬ (x = y) ∧ (x != 0) then !flag && y != 0 else true
    if _k : next then x / y else y % x

def propChoiceDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (if x = y then x == 0 else y != 0)
  let mut a := x
  if flag then a := a + y else a := a - y
  let next := if a % 3 ≤ 1 then !flag else a != 0
  let z ← if next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def propChoiceUnused (x y : UInt64) : UInt64 :=
  let _unused := if True ∧ ¬ False then false else x / 0 == y
  let kept := if False ∨ ¬ True then false else true
  if kept then x + y else x - y

def rangePropChoiceYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := if UInt64.ofNat i % 2 = 0 then a != 0 else a == 0
    if even then a := a + 3 else a := a + 7
  return a

def rangePropChoiceBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if _h : (if (a % 7 = 0 ∨ UInt64.ofNat i ≥ 12) ∧ count ≠ 0 then true else false) then break
  return a

def rangePropChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := if UInt64.ofNat i % 3 ≥ 1 then a != seed else false
    if skip then continue
    a := a + UInt64.ofNat i
    let stop := if !skip then a % 11 == 0 else false
    if stop then break
  return a

def rangePropChoiceJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (if a % 2 = 0 then true else false)
    if even then a := a + 2 else a := a + 5
    let next ← pure (if even then a % 3 == 0 else !even)
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if (if next then a % 13 == 0 else false) then break
  return a

def rangePropChoiceCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag := if ¬ (seed % 3 = 0) then count != 0 else false
  let f := fun x y z : UInt64 =>
    let inner := if flag then x != y else y == z
    if inner then x + y - z else x - y + z
  let mut a := seed
  for i in [:count.toNat] do
    let inner := if a ≥ seed ∧ (a != 0) then flag && a % 5 == 0 else a == seed
    a := f a (UInt64.ofNat i) count
    if inner && flag then break
  return a

def rangePropChoiceBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := if ¬ (seed % 3 = 0) then true else count == 0
  let first : UInt64 := if flag then 0 else 2
  let stop := if (if flag then false else count != 0) then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish := if flag then a % 7 == 0 else false
    if finish then break
    a := a + UInt64.ofNat i
  return a

def rangePropChoiceStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let captured := if a % 5 ≤ 1 then count != 0 else false
    let f : UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y z => do
      let inner := if x < y ∨ y = z then captured || x == y else !captured && y != z
      if _h : inner then return .done (x + y - z)
      else return .yield (x - y + z)
    f a (UInt64.ofNat i) count

def rangePropChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag := if seed ≤ 1 then count != 0 else false
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop := if flag then a % 7 == 0 else false
    if stop then break
  let changed ← pure (if flag then a != seed else count == 0)
  return if changed then a + count else a - count

def propChoiceUnsupportedArm (x y : UInt64) : UInt64 :=
  let flag := if True then false else toString x == toString y
  if flag then x else y

def propChoiceUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := if False then toString x == toString y else true
  x + y

def propChoiceCustomDecision (x y : UInt64) : UInt64 :=
  let flag := @ite Bool (x < y)
    (if h : x < y then .isTrue h else .isFalse h) true false
  if flag then x else y

def rangePropChoiceUnsupportedArm (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let flag := if False then toString a == toString seed else true
    return if flag then .yield (a + 1) else .done a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PropositionChoiceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PropositionChoiceTest.propChoiceLet, PropositionChoiceTest.propChoiceLet, false),
    (`PropositionChoiceTest.propChoiceNested, PropositionChoiceTest.propChoiceNested, false),
    (`PropositionChoiceTest.propChoiceClosed, PropositionChoiceTest.propChoiceClosed, false),
    (`PropositionChoiceTest.propChoiceShadow, PropositionChoiceTest.propChoiceShadow, false),
    (`PropositionChoiceTest.propChoiceCapture, PropositionChoiceTest.propChoiceCapture, false),
    (`PropositionChoiceTest.propChoiceDependent, PropositionChoiceTest.propChoiceDependent, false),
    (`PropositionChoiceTest.propChoiceDo, PropositionChoiceTest.propChoiceDo, false),
    (`PropositionChoiceTest.propChoiceUnused, PropositionChoiceTest.propChoiceUnused, false),
    (`PropositionChoiceTest.rangePropChoiceYield, PropositionChoiceTest.rangePropChoiceYield, true),
    (`PropositionChoiceTest.rangePropChoiceBreak, PropositionChoiceTest.rangePropChoiceBreak, true),
    (`PropositionChoiceTest.rangePropChoiceContinue, PropositionChoiceTest.rangePropChoiceContinue, true),
    (`PropositionChoiceTest.rangePropChoiceJoined, PropositionChoiceTest.rangePropChoiceJoined, true),
    (`PropositionChoiceTest.rangePropChoiceCapture, PropositionChoiceTest.rangePropChoiceCapture, true),
    (`PropositionChoiceTest.rangePropChoiceBounds, PropositionChoiceTest.rangePropChoiceBounds, true),
    (`PropositionChoiceTest.rangePropChoiceStep, PropositionChoiceTest.rangePropChoiceStep, true),
    (`PropositionChoiceTest.rangePropChoiceOuter, PropositionChoiceTest.rangePropChoiceOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: propositional choice extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PropositionChoiceTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`PropositionChoiceTest.propChoiceUnsupportedArm, `PropositionChoiceTest.propChoiceUnusedUnsupported, `PropositionChoiceTest.propChoiceCustomDecision, `PropositionChoiceTest.rangePropChoiceUnsupportedArm] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported propositional choice accepted"
  let boolType := Lean.Expr.const ``Bool []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.false []
  let no := Lean.Expr.const ``Bool.true []
  let left := LeanExe.Source.Scalar.literalExpr 0
  let right := LeanExe.Source.Scalar.literalExpr 1
  let condition := LeanExe.Source.Scalar.Comparison.lt.condition left right
  let evidence := LeanExe.Source.Scalar.Comparison.lt.evidence left right
  let make (result decision first : Lean.Expr) :=
    Lean.mkAppN (.const ``ite [.succ .zero]) #[result, condition, decision, first, no]
  let mismatched := LeanExe.Source.Scalar.Comparison.le.evidence left right
  for argument in [make (.const ``UInt64 []) evidence yes,
      make boolType (.bvar 0) yes, make boolType mismatched yes,
      make boolType evidence one] do
    let scalar := Lean.Expr.letE `flag boolType argument one false
    let step := Lean.Expr.letE `flag boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false
    unless (LeanExe.Extract.Core.extractScalarExprWith [] scalar).isNone do
      throwError "invalid propositional choice accepted in scalar code"
    unless (LeanExe.Extract.Core.extractScalarStepWith [] step).isNone do
      throwError "invalid propositional choice accepted in step code"
  Lean.logInfo "304 native/proposition-choice IR comparisons, four declaration rejection tests and eight raw choice rejection tests passed"
