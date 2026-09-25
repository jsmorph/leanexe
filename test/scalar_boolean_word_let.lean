import LeanExe.Extract.ScalarFunc

namespace BooleanWordLetTest

def boolWordLetOriginal (x y : UInt64) : UInt64 :=
  (let word := x + y; word == 0).toUInt64

def boolWordLetMixed (x y : UInt64) : UInt64 :=
  let outer := x == 0
  (let word := if outer then x + y else x - y
   let flag := word == 0
   let more := word + y
   flag || more == x).toUInt64 + y

def boolWordLetShadow (x y : UInt64) : UInt64 :=
  (let x := x + y; let x := x * 3; x != y).toUInt64 + x

def boolWordLetHelper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  (let word := (let f := fun flag : Bool => if flag then x + y else x - y; f outer)
   if _h : word ≤ x then word == y else word != x).toUInt64

def boolWordLetDependent (x y : UInt64) : UInt64 :=
  (let word := x + y
   let flag := if _h : word < x then word == y else word != 0
   let other := if flag then word + x else word + y
   if _h : flag then other == x else other != y).toUInt64

def boolWordLetUnused (x y : UInt64) : UInt64 :=
  (let _word := x / y; y != 0).toUInt64 + x

def boolWordLetDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (let word := x + y; word != 0)
  let other ← if flag then pure (let word := x - y; word == 0) else pure (let word := x * y; word != 0)
  let mut z := x
  if (let word := if flag then x else y; word == z) then z := z + y else z := z - y
  return z + (let word := if other then z else y; word != 0).toUInt64

def boolWordLetNegated (x y : UInt64) : UInt64 :=
  (!(let word := x + y; word == 0)).toUInt64 +
    (!!(let word := x - y; decide (word < y))).toUInt64

def rangeBoolWordLetYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let word := a + UInt64.ofNat i; word % 7 == 0)
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag then break
  return a

def rangeBoolWordLetJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (let word := a + UInt64.ofNat i; word % 2 == 0)
    let next ← if even then pure (let word := a + seed; word != 0) else pure (let word := a - seed; word == 0)
    if next then a := a + 2 else a := a + 5
    if (let word := if next then a + 1 else a + 2; word % 7 == 0) then break
  return a

def rangeBoolWordLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let word := UInt64.ofNat i + a; word % 3 == 1) then continue
    a := a + UInt64.ofNat i
    if (let word := a - seed; if _h : word < a then word == 0 else word % 7 == 0) then break
  return a

def rangeBoolWordLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (let word := if flag then seed else count; word == 0).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (let word := if flag then a else seed; word != 0) + a
    a := g (let word := UInt64.ofNat i; word % 2 == 0)
    if (let word := a + seed; word % 11 == 0 && outer) then break
  return a + f (let word := a - seed; word == 0)

def rangeBoolWordLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := (let word := seed + 1; word == 0).toUInt64
  let stop := count + (let word := seed - 1; word != 0).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    a := a + (let word := UInt64.ofNat i + a; word % 2 == 0).toUInt64
    if (let word := a - seed; word % 7 == 0) then break
  return a

def rangeBoolWordLetStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (let word := if flag then a else seed; word == 0)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (let word := a - seed; word != 0).toUInt64)
    f (let word := UInt64.ofNat i; word % 2 == 0)

def rangeBoolWordLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (let word := count + seed; word != 0)
  let mut a := seed + (let word := if flag then seed else count; word == 0).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (let word := a - seed; word % 7 == 0) then break
  let changed ← pure (let word := a + seed; word == 0)
  return a + (let word := if changed then a else seed; word != 0).toUInt64

def rangeBoolWordLetUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := (let word := a + UInt64.ofNat i; word != seed)
    a := a + UInt64.ofNat i + 1
    if (let word := a - seed; word % 7 == 0) then break
  return a

def boolWordLetUnsupportedBound (x y : UInt64) : UInt64 :=
  (let _word := UInt64.ofNat (toString x).length; true).toUInt64 + y

def boolWordLetUnsupportedBody (x y : UInt64) : UInt64 :=
  let _unused := (let word := x + y; if word == 0 then true else toString word == toString y)
  x + y

def boolWordLetUnsupportedType (x y : UInt64) : UInt64 :=
  (let number := x.toNat; number == y.toNat).toUInt64

def rangeBoolWordLetUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := (let _word := UInt64.ofNat (toString a).length; false)
    return .yield (a + 1)
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanWordLetTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanWordLetTest.boolWordLetOriginal, BooleanWordLetTest.boolWordLetOriginal, false),
    (`BooleanWordLetTest.boolWordLetMixed, BooleanWordLetTest.boolWordLetMixed, false),
    (`BooleanWordLetTest.boolWordLetShadow, BooleanWordLetTest.boolWordLetShadow, false),
    (`BooleanWordLetTest.boolWordLetHelper, BooleanWordLetTest.boolWordLetHelper, false),
    (`BooleanWordLetTest.boolWordLetDependent, BooleanWordLetTest.boolWordLetDependent, false),
    (`BooleanWordLetTest.boolWordLetUnused, BooleanWordLetTest.boolWordLetUnused, false),
    (`BooleanWordLetTest.boolWordLetDo, BooleanWordLetTest.boolWordLetDo, false),
    (`BooleanWordLetTest.boolWordLetNegated, BooleanWordLetTest.boolWordLetNegated, false),
    (`BooleanWordLetTest.rangeBoolWordLetYield, BooleanWordLetTest.rangeBoolWordLetYield, true),
    (`BooleanWordLetTest.rangeBoolWordLetJoined, BooleanWordLetTest.rangeBoolWordLetJoined, true),
    (`BooleanWordLetTest.rangeBoolWordLetContinue, BooleanWordLetTest.rangeBoolWordLetContinue, true),
    (`BooleanWordLetTest.rangeBoolWordLetCapture, BooleanWordLetTest.rangeBoolWordLetCapture, true),
    (`BooleanWordLetTest.rangeBoolWordLetBounds, BooleanWordLetTest.rangeBoolWordLetBounds, true),
    (`BooleanWordLetTest.rangeBoolWordLetStep, BooleanWordLetTest.rangeBoolWordLetStep, true),
    (`BooleanWordLetTest.rangeBoolWordLetOuter, BooleanWordLetTest.rangeBoolWordLetOuter, true),
    (`BooleanWordLetTest.rangeBoolWordLetUnused, BooleanWordLetTest.rangeBoolWordLetUnused, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean word let extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanWordLetTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanWordLetTest.boolWordLetUnsupportedBound, `BooleanWordLetTest.boolWordLetUnsupportedBody, `BooleanWordLetTest.boolWordLetUnsupportedType, `BooleanWordLetTest.rangeBoolWordLetUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean word let accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.true []
  let scalarLocals : List LeanExe.Extract.Core.ScalarBinding := [.boolean (.u64 1), .word (.u64 9)]
  let stepLocals : List LeanExe.Extract.Core.ScalarStepBinding := [.scalar (.boolean (.u64 1)), .scalar (.word (.u64 9))]
  let mut rawRejections : Nat := 0
  for nondep in [false, true] do
    let make (type value body : Lean.Expr) := Lean.Expr.letE `word type value body nondep
    let comparison := LeanExe.Source.Scalar.BooleanComparison.eq.expr (.bvar 0) one
    for valid in [make wordType (.bvar 1) comparison,
        make wordType one (.bvar 1),
        make wordType one (make boolType (.bvar 1) (.bvar 0))] do
      unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals
          (.letE `unused boolType valid one false)).isSome do
        throwError "valid word binding in Boolean value rejected in scalar code"
      unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
          (.letE `unused boolType valid (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isSome do
        throwError "valid word binding in Boolean value rejected in step code"
    let choice := LeanExe.Source.Scalar.booleanChoiceExpr false yes yes (.bvar 0) yes
    let invalid := [make wordType yes yes, make wordType one one,
      make (.const ``UInt64 [.zero]) one yes, make (.const ``Nat []) one yes,
      make wordType (.bvar 0) yes, make wordType one (.bvar 0),
      make wordType one (.bvar 2), make wordType (.bvar 7) yes, make wordType one (.bvar 7),
      make wordType one (make boolType (.bvar 0) (.bvar 0)),
      make wordType one (make boolType yes (.bvar 1)),
      make wordType one (make wordType one (.bvar 1)),
      make wordType one choice,
      make wordType one (LeanExe.Source.Scalar.BooleanComparison.eq.expr yes one),
      make wordType one (make wordType one (.bvar 0)),
      make wordType one (make boolType yes (make wordType one (.bvar 0)))]
    for argument in invalid do
      unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals
          (.letE `unused boolType argument one false)).isNone do
        throwError "invalid word binding in Boolean value accepted in scalar code"
      rawRejections := rawRejections + 1
      unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
          (.letE `unused boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isNone do
        throwError "invalid word binding in Boolean value accepted in step code"
      rawRejections := rawRejections + 1
  Lean.logInfo m!"304 native/Boolean-word-let IR comparisons, four declaration rejection tests and {rawRejections} raw let rejection tests passed"
