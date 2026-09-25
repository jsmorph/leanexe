import LeanExe.Extract.ScalarFunc

namespace BooleanPropositionTest

def boolPropEqual (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  if a = b then x + y else x - y

def boolPropUnequal (x y : UInt64) : UInt64 :=
  let a := x == y
  let b := decide (x < y)
  if a ≠ b then x + 7 else y - 11

def boolPropLiterals (x y : UInt64) : UInt64 :=
  let flag := x != 0
  if flag = false then x + y else if true ≠ flag then x - y else y

def boolPropDependent (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let f := fun flag : Bool =>
    if _h : flag = outer then
      let g := fun other : Bool => if other ≠ flag then x + y else x - y
      g (y == 0)
    else (flag != outer).toUInt64 + x
  f (y != 0)

def boolPropTruth (x y : UInt64) : UInt64 :=
  let flag := x == 0
  if flag = true then
    if false = false then x / y else x % y
  else if _h : false ≠ true then y / x else y % x

def boolPropChoices (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  if (if a then b else !b) = (if x < y then a else !a) then
    if _h : (a && b) ≠ (a || b) then x + y else x - y
  else if _h : (!(a == b)) = (!!(a != b)) then x / y else y % x

def boolPropDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let mut z := x
  if a = b then z := z + y else z := z - y
  if _h : a ≠ !b then z := z + 3 else z := z - 7
  return z + a.toUInt64

def boolPropEarly (x y : UInt64) : UInt64 := Id.run do
  let flag := decide (x < y)
  let other := y != 0
  if _h : flag = other then return x + y
  if flag ≠ false then return x - y
  return (if true = !other then y / x else x / y)

def rangeBoolPropYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    if first = second then a := a + 3 else a := a + 7
    if _h : first ≠ second then break
  return a

def rangeBoolPropBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let first := a % 7 == 0
    let second := decide (UInt64.ofNat i < 12)
    if first = second then break
  return a

def rangeBoolPropContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := UInt64.ofNat i % 3 == 1
    let second := a == seed
    if _h : first ≠ second then continue
    a := a + UInt64.ofNat i
    if first = false then break
  return a

def rangeBoolPropJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    let other ← pure (UInt64.ofNat i % 2 == 0)
    if even = other then a := a + 2 else a := a + 5
    if _h : (!even) ≠ other then a := a + UInt64.ofNat i else a := a - count
    if even = (a % 13 == 0) then break
  return a

def rangeBoolPropCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => if flag = outer then count else seed
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => if _h : flag ≠ outer then f (!flag) + a else a + 1
    a := g (UInt64.ofNat i % 2 == 0)
    if (a % 11 == 0) ≠ outer then break
  return a + f (a == 0)

def rangeBoolPropBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first : UInt64 := if flag = false then 0 else 1
  let stop := count + (if flag ≠ true then 1 else 0)
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    if even = flag then a := a + 1 else a := a + 3
    if (a % 7 == 0) ≠ flag then break
  return a

def rangeBoolPropStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      if _h : flag = outer then return .done (a + UInt64.ofNat i)
      else if flag ≠ false then return .yield (a - count)
      else return .yield (a + count)
    f (decide (UInt64.ofNat i ≥ 7))

def rangeBoolPropOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + (if flag = false then 3 else 1)
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (a % 7 == 0) ≠ flag then break
  return if _h : (a == seed) = flag then a + count else a - count

def boolPropUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  if flag = (toString x == toString y) then x else y

def boolPropInactiveUnsupported (x y : UInt64) : UInt64 :=
  if true = false then (toString x).length.toUInt64 else x + y

def boolPropCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == 0
  @ite UInt64 (flag = flag) (isTrue rfl) x y

def rangeBoolPropUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    if _h : true ≠ false then return .yield (a + 1)
    else return .done ((toString a).length.toUInt64)
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPropositionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanPropositionTest.boolPropEqual, BooleanPropositionTest.boolPropEqual, false),
    (`BooleanPropositionTest.boolPropUnequal, BooleanPropositionTest.boolPropUnequal, false),
    (`BooleanPropositionTest.boolPropLiterals, BooleanPropositionTest.boolPropLiterals, false),
    (`BooleanPropositionTest.boolPropDependent, BooleanPropositionTest.boolPropDependent, false),
    (`BooleanPropositionTest.boolPropTruth, BooleanPropositionTest.boolPropTruth, false),
    (`BooleanPropositionTest.boolPropChoices, BooleanPropositionTest.boolPropChoices, false),
    (`BooleanPropositionTest.boolPropDo, BooleanPropositionTest.boolPropDo, false),
    (`BooleanPropositionTest.boolPropEarly, BooleanPropositionTest.boolPropEarly, false),
    (`BooleanPropositionTest.rangeBoolPropYield, BooleanPropositionTest.rangeBoolPropYield, true),
    (`BooleanPropositionTest.rangeBoolPropBreak, BooleanPropositionTest.rangeBoolPropBreak, true),
    (`BooleanPropositionTest.rangeBoolPropContinue, BooleanPropositionTest.rangeBoolPropContinue, true),
    (`BooleanPropositionTest.rangeBoolPropJoined, BooleanPropositionTest.rangeBoolPropJoined, true),
    (`BooleanPropositionTest.rangeBoolPropCapture, BooleanPropositionTest.rangeBoolPropCapture, true),
    (`BooleanPropositionTest.rangeBoolPropBounds, BooleanPropositionTest.rangeBoolPropBounds, true),
    (`BooleanPropositionTest.rangeBoolPropStep, BooleanPropositionTest.rangeBoolPropStep, true),
    (`BooleanPropositionTest.rangeBoolPropOuter, BooleanPropositionTest.rangeBoolPropOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean proposition extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanPropositionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanPropositionTest.boolPropUnsupported, `BooleanPropositionTest.boolPropInactiveUnsupported, `BooleanPropositionTest.boolPropCustomDecision, `BooleanPropositionTest.rangeBoolPropUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean proposition accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let stepType := LeanExe.Source.Scalar.Step.resultType .word
  let one := LeanExe.Source.Scalar.literalExpr 1
  let step := LeanExe.Source.Scalar.Step.yieldDirect one
  let left := Lean.Expr.bvar 0
  let right := Lean.Expr.bvar 1
  for unequal in [false, true] do
    let condition := LeanExe.Source.Scalar.booleanRelationCondition unequal left right
    let evidence := LeanExe.Source.Scalar.booleanRelationEvidence unequal left right
    let make (type body condition evidence : Lean.Expr) :=
      Lean.mkAppN (.const ``ite [.succ .zero]) #[type, condition, evidence, body, body]
    let wrongLevel := Lean.mkAppN (.const (if unequal then ``Ne else ``Eq) [.zero]) #[boolType, left, right]
    let wrongType := Lean.mkAppN (.const (if unequal then ``Ne else ``Eq) [.succ .zero]) #[wordType, left, right]
    let wrongLeft := LeanExe.Source.Scalar.booleanRelationCondition unequal one right
    for (badCondition, badEvidence) in [(condition, Lean.Expr.bvar 0),
        (condition, LeanExe.Source.Scalar.booleanRelationEvidence (!unequal) left right),
        (wrongLeft, LeanExe.Source.Scalar.booleanRelationEvidence unequal one right),
        (wrongLevel, evidence), (wrongType, evidence),
        (condition, LeanExe.Source.Scalar.booleanRelationEvidence unequal right left)] do
      unless (LeanExe.Extract.Core.extractScalarExprWith [.boolean (.u64 1), .boolean (.u64 0)]
          (make wordType one badCondition badEvidence)).isNone do
        throwError "invalid propositional Boolean guard accepted in scalar code"
      unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.boolean (.u64 1)), .scalar (.boolean (.u64 0))]
          (make stepType step badCondition badEvidence)).isNone do
        throwError "invalid propositional Boolean guard accepted in step code"
    let negative := Lean.Expr.app (.const ``Not []) condition
    let dependent (type body td fd : Lean.Expr) :=
      Lean.mkAppN (.const ``dite [.succ .zero]) #[type, condition, evidence,
        .lam `h td body .default, .lam `h fd body .default]
    for (td, fd, scalarBody, stepBody) in [(wordType, negative, one, step),
        (condition, condition, one, step),
        (condition, negative, Lean.Expr.bvar 0, LeanExe.Source.Scalar.Step.yieldDirect (.bvar 0))] do
      unless (LeanExe.Extract.Core.extractScalarExprWith [.boolean (.u64 1), .boolean (.u64 0)]
          (dependent wordType scalarBody td fd)).isNone do
        throwError "invalid propositional Boolean proof binder accepted in scalar code"
      unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.boolean (.u64 1)), .scalar (.boolean (.u64 0))]
          (dependent stepType stepBody td fd)).isNone do
        throwError "invalid propositional Boolean proof binder accepted in step code"
    unless (LeanExe.Extract.Core.extractScalarExprWith [.word (.u64 1), .boolean (.u64 0)]
        (make wordType one condition evidence)).isNone do
      throwError "word binding read as Boolean in scalar proposition"
    unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.word (.u64 1)), .scalar (.boolean (.u64 0))]
        (make stepType step condition evidence)).isNone do
      throwError "word binding read as Boolean in step proposition"
  Lean.logInfo "304 native/Boolean-proposition IR comparisons, four declaration rejection tests and forty raw guard rejection tests passed"
