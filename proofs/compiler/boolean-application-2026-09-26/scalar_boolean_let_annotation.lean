import LeanExe.Extract.ScalarFunc

namespace BooleanLetAnnotationTest

def annotatedLetBoolean (x y : UInt64) : UInt64 :=
  (let flag : Id Bool := x == 0; flag && y != 0).toUInt64 + x

def annotatedLetWord (x y : UInt64) : UInt64 :=
  (let value : Id UInt64 := x + y; Id.run value == 0).toUInt64

def annotatedLetNested (x y : UInt64) : UInt64 :=
  (let flag : Id (Id Bool) := x == 0
   let value : Id (Id UInt64) := if flag && y != 0 then x + y else x - y
   let next : Id Bool := Id.run (Id.run value) != 0
   !(next : Bool)).toUInt64 + y

def annotatedLetHelper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    (let saved : Id Bool := flag
     let value : Id UInt64 := if saved && outer then x + y else x - y
     (Id.run value == x) || (saved && !outer)).toUInt64
  f (y != 0)

def annotatedLetUnused (x y : UInt64) : UInt64 :=
  (let _flag : Id (Id Bool) := x == y
   let _word : Id UInt64 := x / y
   x != y).toUInt64 + x

def annotatedLetDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (let saved : Id Bool := x == 0; !saved)
  let next ← if flag then
      pure (let value : Id UInt64 := Id.run (pure (x + y)); Id.run value == y)
    else pure (let value : Id (Id UInt64) := x - y; Id.run (Id.run value) != 0)
  return x + (let saved : Id Bool := next; saved && flag).toUInt64

def annotatedLetNegated (x y : UInt64) : UInt64 :=
  (!(let flag : Id Bool := x == 0; flag && y != 0)).toUInt64 +
    (!!(let value : Id (Id UInt64) := x - y; Id.run (Id.run value) == 0)).toUInt64

def annotatedLetShadow (x y : UInt64) : UInt64 :=
  (let value : Id UInt64 := x + y
   let value : Id (Id UInt64) := Id.run value * 3
   let flag : Id Bool := Id.run (Id.run value) == y
   flag || x == 0).toUInt64 + y

def rangeAnnotatedLetYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let word : Id UInt64 := a + UInt64.ofNat i
                    let stop : Id (Id Bool) := Id.run word % 7 == 0
                    (stop && seed != 0))
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag then break
  return a

def rangeAnnotatedLetJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (let value : Id UInt64 := a + UInt64.ofNat i; Id.run value % 2 == 0)
    let next ← if even then pure (let flag : Id Bool := UInt64.ofNat i == 0; !flag)
      else pure (let flag : Id (Id Bool) := a == seed; flag && even)
    if next then a := a + 2 else a := a + 5
    if (let value : Id UInt64 := a - seed; Id.run value % 7 == 0) then break
  return a

def rangeAnnotatedLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let skip : Id Bool := UInt64.ofNat i % 3 == 1; skip && a != 0) then continue
    a := a + UInt64.ofNat i
    if (let value : Id (Id UInt64) := a - seed; Id.run (Id.run value) % 7 == 0) then break
  return a

def rangeAnnotatedLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (let saved : Id Bool := flag; saved && outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (let value : Id UInt64 := if flag then a else seed; Id.run value != 0) + a
    a := g (let value : Id UInt64 := UInt64.ofNat i; Id.run value % 2 == 0)
    if (let stop : Id Bool := a % 11 == 0; stop && outer) then break
  return a + f (let value : Id UInt64 := a - seed; Id.run value == 0)

def rangeAnnotatedLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := (let value : Id UInt64 := seed + 1; Id.run value == 0).toUInt64
  let stop := count + (let positive : Id (Id Bool) := count != 0; !!positive).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    a := a + (let value : Id (Id UInt64) := UInt64.ofNat i + a; Id.run (Id.run value) % 2 == 0).toUInt64
    if (let stop : Id Bool := a % 7 == 0; stop && seed != 0) then break
  return a

def rangeAnnotatedLetStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (let value : Id UInt64 := if flag then a else seed; Id.run value == 0)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (let saved : Id (Id Bool) := next; !saved).toUInt64)
    f (let value : Id UInt64 := UInt64.ofNat i; Id.run value % 2 == 0)

def rangeAnnotatedLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (let saved : Id Bool := count != 0; saved || seed == 0)
  let mut a := seed + (let value : Id UInt64 := if flag then seed else count; Id.run value == 0).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (let value : Id (Id UInt64) := a - seed; Id.run (Id.run value) % 7 == 0) then break
  let changed ← pure (let saved : Id Bool := a == seed; !saved)
  return a + (let value : Id UInt64 := if changed then a else seed; Id.run value != 0).toUInt64

def rangeAnnotatedLetUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := (let value : Id UInt64 := a + UInt64.ofNat i
                   let saved : Id (Id Bool) := Id.run value != seed
                   !saved)
    a := a + UInt64.ofNat i + 1
    if (let value : Id UInt64 := a - seed; Id.run value % 7 == 0) then break
  return a

def annotatedLetUnsupportedBound (x y : UInt64) : UInt64 :=
  (let _flag : Id (Id Bool) := toString x == toString y; true).toUInt64

def annotatedLetUnsupportedBody (x y : UInt64) : UInt64 :=
  let _unused := (let value : Id UInt64 := x + y
                 if Id.run value == 0 then true else toString x == toString y)
  x + y

def annotatedLetUnsupportedType (x y : UInt64) : UInt64 :=
  (let number : Id Nat := x.toNat; Id.run number == y.toNat).toUInt64

def rangeAnnotatedLetUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := (let _value : Id UInt64 := UInt64.ofNat (toString a).length; false)
    return .yield (a + 1)
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLetAnnotationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLetAnnotationTest.annotatedLetBoolean, BooleanLetAnnotationTest.annotatedLetBoolean, false),
    (`BooleanLetAnnotationTest.annotatedLetWord, BooleanLetAnnotationTest.annotatedLetWord, false),
    (`BooleanLetAnnotationTest.annotatedLetNested, BooleanLetAnnotationTest.annotatedLetNested, false),
    (`BooleanLetAnnotationTest.annotatedLetHelper, BooleanLetAnnotationTest.annotatedLetHelper, false),
    (`BooleanLetAnnotationTest.annotatedLetUnused, BooleanLetAnnotationTest.annotatedLetUnused, false),
    (`BooleanLetAnnotationTest.annotatedLetDo, BooleanLetAnnotationTest.annotatedLetDo, false),
    (`BooleanLetAnnotationTest.annotatedLetNegated, BooleanLetAnnotationTest.annotatedLetNegated, false),
    (`BooleanLetAnnotationTest.annotatedLetShadow, BooleanLetAnnotationTest.annotatedLetShadow, false),
    (`BooleanLetAnnotationTest.rangeAnnotatedLetYield, BooleanLetAnnotationTest.rangeAnnotatedLetYield, true),
    (`BooleanLetAnnotationTest.rangeAnnotatedLetJoined, BooleanLetAnnotationTest.rangeAnnotatedLetJoined, true),
    (`BooleanLetAnnotationTest.rangeAnnotatedLetContinue, BooleanLetAnnotationTest.rangeAnnotatedLetContinue, true),
    (`BooleanLetAnnotationTest.rangeAnnotatedLetCapture, BooleanLetAnnotationTest.rangeAnnotatedLetCapture, true),
    (`BooleanLetAnnotationTest.rangeAnnotatedLetBounds, BooleanLetAnnotationTest.rangeAnnotatedLetBounds, true),
    (`BooleanLetAnnotationTest.rangeAnnotatedLetStep, BooleanLetAnnotationTest.rangeAnnotatedLetStep, true),
    (`BooleanLetAnnotationTest.rangeAnnotatedLetOuter, BooleanLetAnnotationTest.rangeAnnotatedLetOuter, true),
    (`BooleanLetAnnotationTest.rangeAnnotatedLetUnused, BooleanLetAnnotationTest.rangeAnnotatedLetUnused, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: annotated Boolean-value let extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLetAnnotationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanLetAnnotationTest.annotatedLetUnsupportedBound, `BooleanLetAnnotationTest.annotatedLetUnsupportedBody, `BooleanLetAnnotationTest.annotatedLetUnsupportedType, `BooleanLetAnnotationTest.rangeAnnotatedLetUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported annotated Boolean-value let accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.true []
  let scalarLocals : List LeanExe.Extract.Core.ScalarBinding := [.boolean (.u64 1), .word (.u64 9)]
  let stepLocals : List LeanExe.Extract.Core.ScalarStepBinding := [.scalar (.boolean (.u64 1)), .scalar (.word (.u64 9))]
  let wrap (depth : Nat) (base : Lean.Expr) :=
    (List.range depth).foldl (fun type _ => Lean.mkApp (.const ``Id [.zero]) type) base
  let mut rawRejections : Nat := 0
  for depth in [1, 3] do
    let boolean := wrap depth boolType
    let word := wrap depth wordType
    for nondep in [false, true] do
      let make (type value body : Lean.Expr) := Lean.Expr.letE `annotated type value body nondep
      let comparison := LeanExe.Source.Scalar.BooleanComparison.eq.expr (.bvar 0) one
      for valid in [make boolean (.bvar 0) (.bvar 0),
          make word (.bvar 1) comparison, make word one (.bvar 1)] do
        unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals
            (.letE `unused boolType valid one false)).isSome do
          throwError "valid annotated Boolean-value binding rejected in scalar code"
        unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
            (.letE `unused boolType valid (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isSome do
          throwError "valid annotated Boolean-value binding rejected in step code"
      let invalid := [make (.app (.const ``Id [.succ .zero]) boolType) yes yes,
        make (.const ``Id [.zero]) yes yes,
        make (wrap depth (.const ``Nat [])) one yes,
        make boolean one yes, make word yes yes, make boolean yes one,
        make word one (.bvar 0), make boolean (.bvar 1) yes, make word (.bvar 0) yes,
        make word one (make boolean yes (.bvar 1)),
        make (wrap depth (.const ``Bool [.zero])) yes yes,
        make (wrap depth (.const ``UInt64 [.zero])) one yes]
      for argument in invalid do
        unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals
            (.letE `unused boolType argument one false)).isNone do
          throwError "invalid annotated binding accepted in scalar code"
        rawRejections := rawRejections + 1
        unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
            (.letE `unused boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isNone do
          throwError "invalid annotated binding accepted in step code"
        rawRejections := rawRejections + 1
  Lean.logInfo m!"304 native/Boolean-let-annotation IR comparisons, four declaration rejection tests and {rawRejections} raw annotation rejection tests passed"
