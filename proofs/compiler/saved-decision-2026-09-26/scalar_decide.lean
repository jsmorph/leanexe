import LeanExe.Extract.ScalarFunc

namespace DecideTest

def decideLet (x y : UInt64) : UInt64 :=
  let flag := decide (x < y)
  if flag then x + y else x - y

def decideImplicit (x y : UInt64) : UInt64 :=
  let flag : Bool := x ≤ y
  if flag then x + y else x - y

def decideCompound (x y : UInt64) : UInt64 :=
  let flag := decide ((x < y ∧ y ≠ 0) ∨ ¬ (x = y))
  if !flag then x + y else x - y

def decideBoolean (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => if flag then x + y else x - y
  f (decide ((x == y) = true))

def decideChoices (x y : UInt64) : UInt64 :=
  let a := decide (x = y)
  let b := decide (x ≠ y)
  let c := decide (x > y)
  let d := decide (x ≥ y)
  let flag := if x ≤ y then (a || b) && !c else d
  if _h : flag then x / y else y % x

def decideCapture (x y : UInt64) : UInt64 :=
  let outer := decide (x = 0)
  let f := fun flag : Bool =>
    let g := fun a b c : UInt64 =>
      let flag := flag && decide (a < b ∨ b ≥ c)
      if flag || outer then a + b * c else a - b + c
    g x y (x + 1)
  let outer := !outer
  f outer + f (decide (x ≤ y))

def decideDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x < y then pure (decide (x > 0)) else pure (decide (y = 0))
  let mut a := x
  if flag then a := a + y else a := a - y
  let next ← Id.run (pure (decide (a ≤ y ∧ ¬ (x = y))))
  return if !!!next then a * 7 else a + 11

def decideUnused (x y : UInt64) : UInt64 :=
  let _unused := decide (False ∧ x / 0 = y)
  let flag := decide (True ∨ ¬ False)
  if flag && !decide (((x == y) && (y != 0)) = true) then x + y else x - y

def rangeDecideYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := decide (UInt64.ofNat i % 2 = 0 ∧ a ≠ 0)
    a := if flag then a + 3 else a + 7
  return a

def rangeDecideBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let flag ← if a % 7 = 0 then pure true else pure (UInt64.ofNat i ≥ 12)
    if flag then break
  return a

def rangeDecideContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip := decide (UInt64.ofNat i % 3 = 1 ∨ a = seed)
    if skip then continue
    a := a + UInt64.ofNat i
    if decide (a % 11 = 0) then break
  return a

def rangeDecideJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (decide (a % 2 = 0))
    if even then a := a + 2 else a := a + 5
    let next ← if even then pure (decide (a % 3 = 0)) else pure (!even)
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if next && decide (a % 13 = 0) then break
  return a

def rangeDecideCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := decide (seed ≠ 0)
  let f := fun flag : Bool => if flag || outer then count + 3 else seed - 7
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => if flag then f outer + a else f (!outer) - a
    a := g (decide (UInt64.ofNat i % 2 = 0))
    if decide (a % 11 = 0) then break
  return f (decide (a = 0)) + a

def rangeDecideBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag : Bool := seed % 3 ≤ 1
  let first : UInt64 := if flag then 0 else 2
  let stop := if !flag && decide (count > 0) then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    if decide (a % 7 = 0) then break
    a := a + UInt64.ofNat i
  return a

def rangeDecideStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let g : UInt64 → ForInStep UInt64 := fun x =>
        if flag && decide (x ≤ seed ∨ a = 0) then .done (a + x) else .yield (a - count)
      return g (UInt64.ofNat i)
    f (decide (UInt64.ofNat i % 3 = 0))

def rangeDecideOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (decide (count ≠ 0))
  let mut a := if flag then seed + 1 else seed - 1
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if decide (a % 7 = 0) then break
  let changed ← if a = seed then pure (decide (count ≠ 0)) else pure (decide (a > 0))
  return if changed then a + count else a - count

def decideUnsupportedOperand (x y : UInt64) : UInt64 :=
  let flag := decide ((toString x).length.toUInt64 < y)
  if flag then x else y

def decideUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := decide (False ∧ (toString x).length.toUInt64 < y)
  x + y

def decideCustomEvidence (x y : UInt64) : UInt64 :=
  let flag := @Decidable.decide (x < y) (if h : x < y then .isTrue h else .isFalse h)
  if flag then x else y

def rangeDecideUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := decide ((toString a).length.toUInt64 < seed)
    return .yield (a + 1)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end DecideTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`DecideTest.decideLet, DecideTest.decideLet, false),
    (`DecideTest.decideImplicit, DecideTest.decideImplicit, false),
    (`DecideTest.decideCompound, DecideTest.decideCompound, false),
    (`DecideTest.decideBoolean, DecideTest.decideBoolean, false),
    (`DecideTest.decideChoices, DecideTest.decideChoices, false),
    (`DecideTest.decideCapture, DecideTest.decideCapture, false),
    (`DecideTest.decideDo, DecideTest.decideDo, false),
    (`DecideTest.decideUnused, DecideTest.decideUnused, false),
    (`DecideTest.rangeDecideYield, DecideTest.rangeDecideYield, true),
    (`DecideTest.rangeDecideBreak, DecideTest.rangeDecideBreak, true),
    (`DecideTest.rangeDecideContinue, DecideTest.rangeDecideContinue, true),
    (`DecideTest.rangeDecideJoined, DecideTest.rangeDecideJoined, true),
    (`DecideTest.rangeDecideCapture, DecideTest.rangeDecideCapture, true),
    (`DecideTest.rangeDecideBounds, DecideTest.rangeDecideBounds, true),
    (`DecideTest.rangeDecideStep, DecideTest.rangeDecideStep, true),
    (`DecideTest.rangeDecideOuter, DecideTest.rangeDecideOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: decide extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else DecideTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`DecideTest.decideUnsupportedOperand, `DecideTest.decideUnusedUnsupported, `DecideTest.decideCustomEvidence, `DecideTest.rangeDecideUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported decide accepted"
  let boolType := Lean.Expr.const ``Bool []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let two := LeanExe.Source.Scalar.literalExpr 2
  let condition := LeanExe.Source.Scalar.Comparison.lt.condition one two
  let evidence := LeanExe.Source.Scalar.Comparison.lt.evidence one two
  let make (levels : List Lean.Level) (condition evidence : Lean.Expr) :=
    Lean.Expr.app (.app (.const ``Decidable.decide levels) condition) evidence
  for argument in [make [] condition (.bvar 0),
      make [] condition (LeanExe.Source.Scalar.Comparison.le.evidence one two),
      make [.zero] condition evidence, make [] (.const ``Bool.true []) evidence] do
    let scalar := Lean.Expr.letE `flag boolType argument one false
    let step := Lean.Expr.letE `flag boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false
    unless (LeanExe.Extract.Core.extractScalarExprWith [] scalar).isNone do
      throwError "invalid decide expression accepted in scalar code"
    unless (LeanExe.Extract.Core.extractScalarStepWith [] step).isNone do
      throwError "invalid decide expression accepted in step code"
  Lean.logInfo "304 native/decide IR comparisons, four declaration rejection tests and eight raw decision rejection tests passed"
