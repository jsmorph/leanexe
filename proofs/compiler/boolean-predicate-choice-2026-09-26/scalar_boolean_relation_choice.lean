import LeanExe.Extract.ScalarFunc

namespace BooleanRelationChoiceTest

def relationChoiceEqual (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let flag := if a = b then a else !b
  flag.toUInt64 + x

def relationChoiceUnequal (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y != 0
  (if a ≠ b then a == b else decide (a = b)).toUInt64 + y

def relationChoiceNested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let left := if a = false then !b else if b ≠ true then a else !a
  let right := if (if a then b else !b) = (if x < y then a else !a) then left else !left
  (if left ≠ right then !a else b).toUInt64

def relationChoiceCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let value := if flag = outer then decide (flag ≠ false) else !flag
    let g := fun other : Bool => (if other ≠ flag then value else !value).toUInt64 + x
    g (y == 0)
  f (y != 0)

def relationChoiceLiterals (x y : UInt64) : UInt64 :=
  (if true = false then true else false).toUInt64 * x +
  (if false = false then true else false).toUInt64 * y +
  (if true ≠ false then false else true).toUInt64 +
  (if false ≠ true then true else false).toUInt64 * 7

def relationChoiceDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let flag ← pure (if a = b then decide (a ≠ false) else !b)
  let mut z := x
  if _h : flag then z := z + y else z := z - y
  return z + (if flag ≠ a then b else !b).toUInt64

def relationChoiceTruth (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  let first := if a then b else !b
  let second := if a = true then b else !b
  (first == second).toUInt64 + (if first = false then x == y else x != y).toUInt64

def relationChoiceUnused (x y : UInt64) : UInt64 :=
  let _unused := if (x == 0) ≠ (y == 0) then decide (x < y) else decide (x > y)
  x + y

def rangeRelationChoiceYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    let same ← if first = second then pure first else pure (!second)
    a := a + (if same ≠ first then same else second).toUInt64
    if same then break
  return a

def rangeRelationChoiceJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    let other ← pure (UInt64.ofNat i % 2 == 0)
    let next ← if even then pure (if even = other then other else !other) else pure (if even ≠ other then even else !even)
    if next then a := a + 2 else a := a + 5
    if (if next = even then a % 7 == 0 else a % 11 == 0) then break
  return a

def rangeRelationChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := UInt64.ofNat i % 3 == 1
    let second := a == seed
    let skip := if first ≠ second then first else !second
    if _h : skip then continue
    a := a + UInt64.ofNat i
    if (if first = false then second else !second) then break
  return a

def rangeRelationChoiceCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (if flag = outer then flag else !flag).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (if flag ≠ outer then outer else !outer) + a
    a := g (UInt64.ofNat i % 2 == 0)
    if (if (a % 11 == 0) ≠ outer then outer else !outer) then break
  return a + f (a == 0)

def rangeRelationChoiceBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := (if flag = false then flag else !flag).toUInt64
  let stop := count + (if flag ≠ true then !flag else flag).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    a := a + (if even = flag then flag else !even).toUInt64
    if (if (a % 7 == 0) ≠ flag then even else flag) then break
  return a

def rangeRelationChoiceStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (if flag = outer then !flag else outer)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (if flag ≠ false then flag else !outer).toUInt64)
    f (if (UInt64.ofNat i ≥ 7 : Bool) = outer then outer else !outer)

def rangeRelationChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + (if flag = false then true else false).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (if (a % 7 == 0) ≠ flag then flag else !flag) then break
  let changed ← if a = seed then pure (if (a == 0) = flag then flag else !flag) else pure (if flag ≠ false then true else false)
  return a + (if changed = flag then changed else flag).toUInt64

def rangeRelationChoiceUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := a == seed
    let _unused := if flag = (UInt64.ofNat i == 0) then !flag else flag
    a := a + UInt64.ofNat i + 1
    if flag then break
  return a

def relationChoiceUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  (if flag = (toString x == toString y) then flag else !flag).toUInt64

def relationChoiceInactiveUnsupported (x y : UInt64) : UInt64 :=
  let _unused := if true ≠ false then true else toString x == toString y
  x + y

def relationChoiceCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let value := @ite Bool (flag = flag) (isTrue rfl) flag (!flag)
  value.toUInt64 + y

def rangeRelationChoiceUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := if (a == seed) ≠ false then true else toString a == toString seed
    return .yield (a + 1)
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanRelationChoiceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanRelationChoiceTest.relationChoiceEqual, BooleanRelationChoiceTest.relationChoiceEqual, false),
    (`BooleanRelationChoiceTest.relationChoiceUnequal, BooleanRelationChoiceTest.relationChoiceUnequal, false),
    (`BooleanRelationChoiceTest.relationChoiceNested, BooleanRelationChoiceTest.relationChoiceNested, false),
    (`BooleanRelationChoiceTest.relationChoiceCapture, BooleanRelationChoiceTest.relationChoiceCapture, false),
    (`BooleanRelationChoiceTest.relationChoiceLiterals, BooleanRelationChoiceTest.relationChoiceLiterals, false),
    (`BooleanRelationChoiceTest.relationChoiceDo, BooleanRelationChoiceTest.relationChoiceDo, false),
    (`BooleanRelationChoiceTest.relationChoiceTruth, BooleanRelationChoiceTest.relationChoiceTruth, false),
    (`BooleanRelationChoiceTest.relationChoiceUnused, BooleanRelationChoiceTest.relationChoiceUnused, false),
    (`BooleanRelationChoiceTest.rangeRelationChoiceYield, BooleanRelationChoiceTest.rangeRelationChoiceYield, true),
    (`BooleanRelationChoiceTest.rangeRelationChoiceJoined, BooleanRelationChoiceTest.rangeRelationChoiceJoined, true),
    (`BooleanRelationChoiceTest.rangeRelationChoiceContinue, BooleanRelationChoiceTest.rangeRelationChoiceContinue, true),
    (`BooleanRelationChoiceTest.rangeRelationChoiceCapture, BooleanRelationChoiceTest.rangeRelationChoiceCapture, true),
    (`BooleanRelationChoiceTest.rangeRelationChoiceBounds, BooleanRelationChoiceTest.rangeRelationChoiceBounds, true),
    (`BooleanRelationChoiceTest.rangeRelationChoiceStep, BooleanRelationChoiceTest.rangeRelationChoiceStep, true),
    (`BooleanRelationChoiceTest.rangeRelationChoiceOuter, BooleanRelationChoiceTest.rangeRelationChoiceOuter, true),
    (`BooleanRelationChoiceTest.rangeRelationChoiceUnused, BooleanRelationChoiceTest.rangeRelationChoiceUnused, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean-relation choice extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanRelationChoiceTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanRelationChoiceTest.relationChoiceUnsupported, `BooleanRelationChoiceTest.relationChoiceInactiveUnsupported, `BooleanRelationChoiceTest.relationChoiceCustomDecision, `BooleanRelationChoiceTest.rangeRelationChoiceUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean-relation choice accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.true []
  let no := Lean.Expr.const ``Bool.false []
  let left := Lean.Expr.bvar 0
  let right := Lean.Expr.bvar 1
  let make (condition evidence yes no : Lean.Expr) (levels : List Lean.Level := [.succ .zero]) :=
    Lean.mkAppN (.const ``ite levels) #[boolType, condition, evidence, yes, no]
  for unequal in [false, true] do
    let condition := LeanExe.Source.Scalar.booleanRelationCondition unequal left right
    let evidence := LeanExe.Source.Scalar.booleanRelationEvidence unequal left right
    let wrongLevel := Lean.mkAppN (.const (if unequal then ``Ne else ``Eq) [.zero]) #[boolType, left, right]
    let wrongType := Lean.mkAppN (.const (if unequal then ``Ne else ``Eq) [.succ .zero]) #[wordType, left, right]
    let wrongLeft := LeanExe.Source.Scalar.booleanRelationCondition unequal one right
    let invalid := [(condition, Lean.Expr.bvar 0),
      (condition, LeanExe.Source.Scalar.booleanRelationEvidence (!unequal) left right),
      (wrongLeft, LeanExe.Source.Scalar.booleanRelationEvidence unequal one right),
      (wrongLevel, evidence), (wrongType, evidence),
      (condition, LeanExe.Source.Scalar.booleanRelationEvidence unequal right left)]
    for argument in invalid.map (fun (condition, evidence) => make condition evidence yes no) ++
        [make condition evidence one no, make condition evidence yes one,
         make condition evidence yes no [.zero]] do
      unless (LeanExe.Extract.Core.extractScalarExprWith [.boolean (.u64 1), .boolean (.u64 0)]
          (.letE `unused boolType argument one false)).isNone do
        throwError "invalid Boolean relation choice accepted in scalar code"
      unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.boolean (.u64 1)), .scalar (.boolean (.u64 0))]
          (.letE `unused boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isNone do
        throwError "invalid Boolean relation choice accepted in step code"
    unless (LeanExe.Extract.Core.extractScalarExprWith [.word (.u64 1), .boolean (.u64 0)]
        (.letE `unused boolType (make condition evidence yes no) one false)).isNone do
      throwError "word binding read as Boolean in scalar choice"
    unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.word (.u64 1)), .scalar (.boolean (.u64 0))]
        (.letE `unused boolType (make condition evidence yes no) (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isNone do
      throwError "word binding read as Boolean in step choice"
  Lean.logInfo "304 native/Boolean-relation-choice IR comparisons, four declaration rejection tests and forty raw choice rejection tests passed"
