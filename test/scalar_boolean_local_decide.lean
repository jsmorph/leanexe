import LeanExe.Extract.ScalarFunc

namespace BooleanLocalDecideTest

def localDecideEqual (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  (decide (a = b)).toUInt64 + (decide (a ≠ b)).toUInt64 * 3

def localDecideTruth (x y : UInt64) : UInt64 :=
  let flag := x != y
  (decide flag).toUInt64 + (decide (flag = true)).toUInt64 * 7

def localDecideImplicit (x y : UInt64) : UInt64 :=
  let a := x != 0
  let b := y == 0
  let same : Bool := a = b
  let different : Bool := a ≠ b
  (same && different).toUInt64 + (same || different).toUInt64

def localDecideNested (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y == 0
  let first := decide ((decide (a = b)) ≠ (decide (a = false)))
  if _h : !first then x + y else x - y

def localDecideLiterals (x y : UInt64) : UInt64 :=
  (decide (true = true)).toUInt64 * x + (decide (false ≠ false)).toUInt64 * y +
    (decide (false = false)).toUInt64 * 3 + (decide (true ≠ false)).toUInt64 * 7 +
    (decide ((x == y) = true)).toUInt64

def localDecideCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let g := fun other : Bool => (decide (flag = other)).toUInt64 + (decide (other ≠ outer)).toUInt64
    g (decide (flag ≠ outer)) + x
  f (y == 0)

def localDecideDo (x y : UInt64) : UInt64 := Id.run do
  let a ← if x = y then pure true else pure (decide (x > 0))
  let b ← pure (y != 0)
  let same ← if a then pure (decide (a = b)) else pure (decide (a ≠ b))
  let mut z := x
  if same then z := z + y else z := z - y
  return z + (decide same).toUInt64

def localDecideChoices (x y : UInt64) : UInt64 :=
  let a := x == 0
  let b := y != 0
  if (if a then b else !b) = (if x < y then a else !a) then
    if _h : (a && b) ≠ (a || b) then x + y else x - y
  else if _h : !(a == b) = !!(a != b) then x / y else y % x

def rangeLocalDecideYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even := a % 2 == 0
    let other := UInt64.ofNat i % 3 == 0
    let same ← pure (decide (even = other))
    a := a + same.toUInt64
    if !even ≠ other then break
  return a

def rangeLocalDecideJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    let other ← pure (UInt64.ofNat i % 2 == 0)
    if even = other then a := a + 2 else a := a + 5
    if _h : !even ≠ other then a := a + UInt64.ofNat i else a := a - count
    if even = (a % 13 == 0) then break
  return a

def rangeLocalDecideContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first := UInt64.ofNat i % 3 == 1
    let second := a == seed
    let skip : Bool := first ≠ second
    if _h : skip then continue
    a := a + UInt64.ofNat i
    if decide (first = false) then break
  return a

def rangeLocalDecideCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (decide (flag = outer)).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (decide (flag ≠ outer)) + a
    a := g (UInt64.ofNat i % 2 == 0)
    if decide ((a % 11 == 0) ≠ outer) then break
  return a + f (decide (a == 0))

def rangeLocalDecideBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag := decide (seed % 3 ≤ 1)
  let first := (decide (flag = false)).toUInt64
  let stop := count + (decide (flag ≠ true)).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let even := UInt64.ofNat i % 2 == 0
    a := a + (decide (even = flag)).toUInt64
    if decide ((a % 7 == 0) ≠ flag) then break
  return a

def rangeLocalDecideStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let same ← pure (decide (flag = outer))
      if _h : same then return .done (a + UInt64.ofNat i)
      else return .yield (a + (decide (flag ≠ false)).toUInt64)
    f (decide ((UInt64.ofNat i ≥ 7 : Bool) = outer))

def rangeLocalDecideOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (count != 0)
  let mut a := seed + (decide (flag = false)).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if decide ((a % 7 == 0) ≠ flag) then break
  let changed ← if a = seed then pure (decide ((a == 0) = flag)) else pure (decide (flag ≠ false))
  return a + (decide (changed = flag)).toUInt64

def rangeLocalDecideUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := decide ((a == seed) = (UInt64.ofNat i == 0))
    let flag := decide ((a == 0) ≠ false)
    a := a + flag.toUInt64
    if _h : flag then break
  return a

def localDecideUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  (decide (flag = (toString x == toString y))).toUInt64

def localDecideInactiveUnsupported (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let _unused := decide ((if true then flag else (toString x == toString y)) = false)
  x + y

def localDecideCustomDecision (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let value := @Decidable.decide (flag = flag) (isTrue rfl)
  if value then x else y

def rangeLocalDecideUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := decide ((a == seed) ≠ (toString a == toString seed))
    return .yield (a + 1)
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLocalDecideTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLocalDecideTest.localDecideEqual, BooleanLocalDecideTest.localDecideEqual, false),
    (`BooleanLocalDecideTest.localDecideTruth, BooleanLocalDecideTest.localDecideTruth, false),
    (`BooleanLocalDecideTest.localDecideImplicit, BooleanLocalDecideTest.localDecideImplicit, false),
    (`BooleanLocalDecideTest.localDecideNested, BooleanLocalDecideTest.localDecideNested, false),
    (`BooleanLocalDecideTest.localDecideLiterals, BooleanLocalDecideTest.localDecideLiterals, false),
    (`BooleanLocalDecideTest.localDecideCapture, BooleanLocalDecideTest.localDecideCapture, false),
    (`BooleanLocalDecideTest.localDecideDo, BooleanLocalDecideTest.localDecideDo, false),
    (`BooleanLocalDecideTest.localDecideChoices, BooleanLocalDecideTest.localDecideChoices, false),
    (`BooleanLocalDecideTest.rangeLocalDecideYield, BooleanLocalDecideTest.rangeLocalDecideYield, true),
    (`BooleanLocalDecideTest.rangeLocalDecideJoined, BooleanLocalDecideTest.rangeLocalDecideJoined, true),
    (`BooleanLocalDecideTest.rangeLocalDecideContinue, BooleanLocalDecideTest.rangeLocalDecideContinue, true),
    (`BooleanLocalDecideTest.rangeLocalDecideCapture, BooleanLocalDecideTest.rangeLocalDecideCapture, true),
    (`BooleanLocalDecideTest.rangeLocalDecideBounds, BooleanLocalDecideTest.rangeLocalDecideBounds, true),
    (`BooleanLocalDecideTest.rangeLocalDecideStep, BooleanLocalDecideTest.rangeLocalDecideStep, true),
    (`BooleanLocalDecideTest.rangeLocalDecideOuter, BooleanLocalDecideTest.rangeLocalDecideOuter, true),
    (`BooleanLocalDecideTest.rangeLocalDecideUnused, BooleanLocalDecideTest.rangeLocalDecideUnused, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean-local decide extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLocalDecideTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanLocalDecideTest.localDecideUnsupported, `BooleanLocalDecideTest.localDecideInactiveUnsupported, `BooleanLocalDecideTest.localDecideCustomDecision, `BooleanLocalDecideTest.rangeLocalDecideUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean-local decide accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let left := Lean.Expr.bvar 0
  let right := Lean.Expr.bvar 1
  let make (condition evidence : Lean.Expr) (levels : List Lean.Level := []) :=
    Lean.mkAppN (.const ``Decidable.decide levels) #[condition, evidence]
  let word (argument : Lean.Expr) := Lean.Expr.app (.const ``Bool.toUInt64 []) argument
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
    for argument in invalid.map (fun (condition, evidence) => make condition evidence) ++
        [make condition evidence [.zero]] do
      unless (LeanExe.Extract.Core.extractScalarExprWith [.boolean (.u64 1), .boolean (.u64 0)]
          (word argument)).isNone do
        throwError "invalid Boolean decision accepted in scalar code"
      unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.boolean (.u64 1)), .scalar (.boolean (.u64 0))]
          (LeanExe.Source.Scalar.Step.yieldDirect (word argument))).isNone do
        throwError "invalid Boolean decision accepted in step code"
    unless (LeanExe.Extract.Core.extractScalarExprWith [.word (.u64 1), .boolean (.u64 0)]
        (word (make condition evidence))).isNone do
      throwError "word binding read as Boolean in scalar decision"
    unless (LeanExe.Extract.Core.extractScalarStepWith [.scalar (.word (.u64 1)), .scalar (.boolean (.u64 0))]
        (LeanExe.Source.Scalar.Step.yieldDirect (word (make condition evidence)))).isNone do
      throwError "word binding read as Boolean in step decision"
  Lean.logInfo "304 native/Boolean-local-decide IR comparisons, four declaration rejection tests and thirty-two raw decision rejection tests passed"
