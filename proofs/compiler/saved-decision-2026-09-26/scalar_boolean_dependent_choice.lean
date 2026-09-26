import LeanExe.Extract.ScalarFunc

namespace BooleanDependentChoiceTest

def dependentChoiceEqual (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let flag := if _h : a = b then b else !b
  flag.toUInt64 + x

def dependentChoiceProposition (x y : UInt64) : UInt64 :=
  let flag := if _h : x < y then x == 0 else y != 0
  flag.toUInt64 + y

def dependentChoiceNested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  let flag := if _h : a then
      if _k : a ≠ b then decide (a = b) else !b
    else if _j : x ≤ y then a == b else a != b
  flag.toUInt64

def dependentChoiceCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let value := if _h : flag = outer then
        (let g := fun z : UInt64 => z + x; g y) == x
      else !flag
    (if _k : value then outer else !outer).toUInt64 + x
  f (y != 0)

def dependentChoiceLiterals (x y : UInt64) : UInt64 :=
  (if _h : True then true else false).toUInt64 * x +
  (if _h : False then true else false).toUInt64 * y +
  (if _h : true ≠ false then false else true).toUInt64 +
  (if _h : false = false then true else false).toUInt64 * 7

def dependentChoiceDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let flag ← pure (if _h : a = b then decide (a ≠ false) else !b)
  let mut z := x
  if _h : flag then z := z + y else z := z - y
  return z + (if _h : flag ≠ a then b else !b).toUInt64

def dependentChoiceTruth (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  let first := if _h : a then b else !b
  let second := if _h : a = true then b else !b
  (first == second).toUInt64 + (if _h : first = false then x == y else x != y).toUInt64

def dependentChoiceUnused (x y : UInt64) : UInt64 :=
  let _unused := if _h : (x == 0) ≠ (y == 0) then decide (x < y) else decide (x > y)
  x + y

def rangeDependentChoiceYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := a % 2 == 0
    let second := UInt64.ofNat i % 3 == 0
    let flag ← pure (if _h : first ≠ second then !second else first)
    a := a + (if _k : flag then first else !second).toUInt64
    if flag then break
  return a

def rangeDependentChoiceJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    let other ← pure (UInt64.ofNat i % 2 == 0)
    let next ← if even then pure (if _h : even = other then other else !other) else pure (if _h : even ≠ other then even else !even)
    if next then a := a + 2 else a := a + 5
    if (if _h : next = even then a % 7 == 0 else a % 11 == 0) then break
  return a

def rangeDependentChoiceContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := UInt64.ofNat i % 3 == 1
    let second := a == seed
    let skip := if _h : first ≠ second then first else !second
    if _h : skip then continue
    a := a + UInt64.ofNat i
    if (if _h : first = false then second else !second) then break
  return a

def rangeDependentChoiceCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (if _h : flag = outer then flag else !flag).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (if _h : flag ≠ outer then outer else !outer) + a
    a := g (UInt64.ofNat i % 2 == 0)
    if (if _h : (a % 11 == 0) ≠ outer then outer else !outer) then break
  return a + f (a == 0)

def rangeDependentChoiceBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := (if _h : flag = false then flag else !flag).toUInt64
  let stop := count + (if _h : flag ≠ true then !flag else flag).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    a := a + (if _h : even = flag then flag else !even).toUInt64
    if (if _h : a ≤ seed then even else flag) then break
  return a

def rangeDependentChoiceStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (if _h : flag = outer then !flag else outer)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (if _h : flag ≠ false then flag else !outer).toUInt64)
    f (if _h : (UInt64.ofNat i ≥ 7 : Bool) = outer then outer else !outer)

def rangeDependentChoiceOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + (if _h : flag = false then true else false).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (if _h : (a % 7 == 0) ≠ flag then flag else !flag) then break
  let changed ← if a = seed then pure (if _h : (a == 0) = flag then flag else !flag) else pure (if _h : flag ≠ false then true else false)
  return a + (if _h : changed = flag then changed else flag).toUInt64

def rangeDependentChoiceUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := a == seed
    let _unused := if _h : flag = (UInt64.ofNat i == 0) then !flag else flag
    a := a + UInt64.ofNat i + 1
    if flag then break
  return a

def dependentChoiceUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  (if _h : flag = (toString x == toString y) then flag else !flag).toUInt64

def dependentChoiceInactiveUnsupported (x y : UInt64) : UInt64 :=
  let _unused := if _h : true ≠ false then true else toString x == toString y
  x + y

def dependentChoiceCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let value := @dite Bool (flag = flag) (isTrue rfl) (fun _ => flag) (fun _ => !flag)
  value.toUInt64 + y

def rangeDependentChoiceUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := if _h : (a == seed) ≠ false then true else toString a == toString seed
    return .yield (a + 1)
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanDependentChoiceTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanDependentChoiceTest.dependentChoiceEqual, BooleanDependentChoiceTest.dependentChoiceEqual, false),
    (`BooleanDependentChoiceTest.dependentChoiceProposition, BooleanDependentChoiceTest.dependentChoiceProposition, false),
    (`BooleanDependentChoiceTest.dependentChoiceNested, BooleanDependentChoiceTest.dependentChoiceNested, false),
    (`BooleanDependentChoiceTest.dependentChoiceCapture, BooleanDependentChoiceTest.dependentChoiceCapture, false),
    (`BooleanDependentChoiceTest.dependentChoiceLiterals, BooleanDependentChoiceTest.dependentChoiceLiterals, false),
    (`BooleanDependentChoiceTest.dependentChoiceDo, BooleanDependentChoiceTest.dependentChoiceDo, false),
    (`BooleanDependentChoiceTest.dependentChoiceTruth, BooleanDependentChoiceTest.dependentChoiceTruth, false),
    (`BooleanDependentChoiceTest.dependentChoiceUnused, BooleanDependentChoiceTest.dependentChoiceUnused, false),
    (`BooleanDependentChoiceTest.rangeDependentChoiceYield, BooleanDependentChoiceTest.rangeDependentChoiceYield, true),
    (`BooleanDependentChoiceTest.rangeDependentChoiceJoined, BooleanDependentChoiceTest.rangeDependentChoiceJoined, true),
    (`BooleanDependentChoiceTest.rangeDependentChoiceContinue, BooleanDependentChoiceTest.rangeDependentChoiceContinue, true),
    (`BooleanDependentChoiceTest.rangeDependentChoiceCapture, BooleanDependentChoiceTest.rangeDependentChoiceCapture, true),
    (`BooleanDependentChoiceTest.rangeDependentChoiceBounds, BooleanDependentChoiceTest.rangeDependentChoiceBounds, true),
    (`BooleanDependentChoiceTest.rangeDependentChoiceStep, BooleanDependentChoiceTest.rangeDependentChoiceStep, true),
    (`BooleanDependentChoiceTest.rangeDependentChoiceOuter, BooleanDependentChoiceTest.rangeDependentChoiceOuter, true),
    (`BooleanDependentChoiceTest.rangeDependentChoiceUnused, BooleanDependentChoiceTest.rangeDependentChoiceUnused, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: dependent Boolean choice extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanDependentChoiceTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanDependentChoiceTest.dependentChoiceUnsupported, `BooleanDependentChoiceTest.dependentChoiceInactiveUnsupported, `BooleanDependentChoiceTest.dependentChoiceCustomDecision, `BooleanDependentChoiceTest.rangeDependentChoiceUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported dependent Boolean choice accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.bvar 1
  let no := Lean.Expr.bvar 2
  let left := Lean.Expr.bvar 0
  let right := Lean.Expr.bvar 1
  let make (condition evidence td yes fd no : Lean.Expr) (levels : List Lean.Level := [.succ .zero]) :=
    Lean.mkAppN (.const ``dite levels) #[boolType, condition, evidence,
      .lam `yes td yes .default, .lam `no fd no .default]
  let mut rawRejections : Nat := 0
  for unequal in [false, true] do
    let condition := LeanExe.Source.Scalar.booleanRelationCondition unequal left right
    let evidence := LeanExe.Source.Scalar.booleanRelationEvidence unequal left right
    let negated := Lean.mkApp (.const ``Not []) condition
    let valid := make condition evidence condition yes negated no
    unless (LeanExe.Extract.Core.extractScalarExprWith [.boolean (.u64 1), .boolean (.u64 0)]
        (.letE `unused boolType valid one false)).isSome do
      throwError "valid captured Boolean proof branch rejected in scalar code"
    unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.boolean (.u64 1)), .scalar (.boolean (.u64 0))]
        (.letE `unused boolType valid (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isSome do
      throwError "valid captured Boolean proof branch rejected in step code"
    let wrongLevel := Lean.mkAppN (.const (if unequal then ``Ne else ``Eq) [.zero]) #[boolType, left, right]
    let wrongType := Lean.mkAppN (.const (if unequal then ``Ne else ``Eq) [.succ .zero]) #[wordType, left, right]
    let wrongLeft := LeanExe.Source.Scalar.booleanRelationCondition unequal one right
    let invalid := [(condition, Lean.Expr.bvar 0),
      (condition, LeanExe.Source.Scalar.booleanRelationEvidence (!unequal) left right),
      (wrongLeft, LeanExe.Source.Scalar.booleanRelationEvidence unequal one right),
      (wrongLevel, evidence), (wrongType, evidence),
      (condition, LeanExe.Source.Scalar.booleanRelationEvidence unequal right left)]
    let nestedRead := Lean.Expr.letE `local boolType (.const ``Bool.true []) (.bvar 1) false
    for argument in invalid.map (fun (c, e) => make c e c yes (Lean.mkApp (.const ``Not []) c) no) ++
        [make condition evidence condition one negated no,
         make condition evidence condition yes negated one,
         make condition evidence boolType yes negated no,
         make condition evidence condition yes condition no,
         make condition evidence condition (.bvar 0) negated no,
         make condition evidence condition yes negated (.bvar 0),
         make condition evidence condition nestedRead negated no,
         make condition evidence condition yes negated nestedRead,
         make condition evidence condition (.mdata {} (.bvar 0)) negated no,
         make condition evidence condition yes negated no [.zero],
         Lean.mkAppN (.const ``dite [.succ .zero]) #[boolType, condition, evidence, yes, no]] do
      unless (LeanExe.Extract.Core.extractScalarExprWith [.boolean (.u64 1), .boolean (.u64 0)]
          (.letE `unused boolType argument one false)).isNone do
        throwError "invalid dependent Boolean choice accepted in scalar code"
      rawRejections := rawRejections + 1
      unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.boolean (.u64 1)), .scalar (.boolean (.u64 0))]
          (.letE `unused boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isNone do
        throwError "invalid dependent Boolean choice accepted in step code"
      rawRejections := rawRejections + 1
    unless (LeanExe.Extract.Core.extractScalarExprWith [.word (.u64 1), .boolean (.u64 0)]
        (.letE `unused boolType valid one false)).isNone do
      throwError "word binding read as Boolean in scalar dependent choice"
    rawRejections := rawRejections + 1
    unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.word (.u64 1)), .scalar (.boolean (.u64 0))]
        (.letE `unused boolType valid (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isNone do
      throwError "word binding read as Boolean in step dependent choice"
    rawRejections := rawRejections + 1
  Lean.logInfo m!"304 native/dependent-Boolean-choice IR comparisons, four declaration rejection tests and {rawRejections} raw choice rejection tests passed"
