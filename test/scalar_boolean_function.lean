import LeanExe.Extract.ScalarFunc

namespace BooleanFunctionTest

def boolFnConditional (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x < y then pure (x == 0) else pure (y != 0)
  return if flag then x + y else x - y

def boolFnLocalGuard (x y : UInt64) : UInt64 := Id.run do
  let saved := x == y
  let flag ← if saved then pure (!saved) else pure (x != 0)
  return if flag then x + y else x - y

def boolFnNested (x y : UInt64) : UInt64 := Id.run do
  let flag ← if x == y then Id.run (pure (x != 0)) else
    if x < y then pure (y == 0) else pure (x == 0)
  return if flag then x + y else x - y

def boolFnDirect (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => if flag then x * 3 + y else x - y * 5
  f true + f false + f (x == y) + f (if x < y then x != 0 else y == 0)

def boolFnShadow (x y : UInt64) : UInt64 :=
  let flag := x == 0
  let f := fun flag : Bool =>
    let g := fun other : Bool => if flag && !other then x + y else x - y
    let flag := !flag
    g flag
  let flag := !flag
  f flag + f (x == y)

def boolFnCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    let g := fun a b c : UInt64 => if flag || outer then a + b * c else a - b / c
    g x y (x + 1)
  let g := fun a b : UInt64 => f (a != b) + f (a == 0 && b != 0)
  g x y

def boolFnAnnotation (x y : UInt64) : UInt64 := Id.run do
  let f : Bool → Id (Id UInt64) := fun flag => pure (pure (if flag then x + y else x - y))
  let a : UInt64 ← f (x == 0)
  let flag ← if a < y then pure (a != 0) else pure (y == 0)
  return if flag then a + 7 else a - 11

def boolFnUnused (x y : UInt64) : UInt64 :=
  let _unused := fun flag : Bool => if flag then x / 0 else y % 0
  let f := fun flag : Bool => if _h : flag then x / y else y % x
  f (if x ≤ y then x != 0 else y == 0)

def rangeBoolFnYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← if UInt64.ofNat i % 2 = 0 then pure (a != 0) else pure (a == 0)
    a := if flag then a + 3 else a + 7
  return a

def rangeBoolFnBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let flag ← if a % 7 = 0 then pure true else pure (UInt64.ofNat i == 12)
    if flag then break
  return a

def rangeBoolFnContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip ← if UInt64.ofNat i % 3 = 1 then pure (a != seed) else pure false
    if skip then continue
    a := a + UInt64.ofNat i
    if a % 11 == 0 then break
  return a

def rangeBoolFnJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← if a % 2 = 0 then pure true else pure false
    if even then a := a + 2 else a := a + 5
    let next ← if even then pure (a % 3 == 0) else pure (!even)
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    if next && a % 13 == 0 then break
  return a

def rangeBoolFnCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => if flag || outer then count + 3 else seed - 7
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => if flag then f outer + a else f (!outer) - a
    a := g (UInt64.ofNat i % 2 == 0)
    if a % 11 == 0 then break
  return f (a == 0) + a

def rangeBoolFnBounds (count seed : UInt64) : UInt64 := Id.run do
  let f := fun flag : Bool => if flag then count else if count == 0 then 0 else count - 1
  let stop := f (seed % 2 == 0)
  let mut a := seed
  for i in [0:stop.toNat:2] do
    let flag ← if a < seed then pure (UInt64.ofNat i == 0) else pure (a % 7 == 0)
    if flag then break
    a := a + UInt64.ofNat i
  return a

def rangeBoolFnStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let g : Bool → ForInStep UInt64 := fun inner =>
        if flag && !inner then .done (a + UInt64.ofNat i) else .yield (a - count)
      return g (if a ≤ seed then outer else !outer)
    f (UInt64.ofNat i % 3 == 0)

def rangeBoolFnOuter (count seed : UInt64) : UInt64 := Id.run do
  let f := fun flag : Bool => if flag then seed + 1 else seed - 1
  let mut a := f (count != 0)
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if a % 7 == 0 then break
  let changed ← if a = seed then pure (count != 0) else pure (a != 0)
  return if changed then a + count else a - count

def boolFnUnusedUnsupported (x y : UInt64) : UInt64 :=
  let _unused := fun flag : Bool => if flag then (toString x).length.toUInt64 else y
  x + y

def boolFnUnsupportedArgument (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => if flag then x else y
  f (toString x == toString y)

def boolFnBooleanResult (x y : UInt64) : UInt64 :=
  let f := fun flag : Bool => !flag
  if f (x == y) then x else y

def rangeBoolFnUnusedUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused : Bool → Id (ForInStep UInt64) := fun flag =>
      pure (if flag then .yield ((toString a).length.toUInt64) else .done a)
    return .yield (a + 1)

def rangeResultFunctionBool (n seed : UInt64) : UInt64 :=
  forIn (m := Id) [:n.toNat] seed fun _ a =>
    let _bad : Bool → ForInStep UInt64 := fun _ => .done a
    .yield (a + 1)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanFunctionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanFunctionTest.boolFnConditional, BooleanFunctionTest.boolFnConditional, false),
    (`BooleanFunctionTest.boolFnLocalGuard, BooleanFunctionTest.boolFnLocalGuard, false),
    (`BooleanFunctionTest.boolFnNested, BooleanFunctionTest.boolFnNested, false),
    (`BooleanFunctionTest.boolFnDirect, BooleanFunctionTest.boolFnDirect, false),
    (`BooleanFunctionTest.boolFnShadow, BooleanFunctionTest.boolFnShadow, false),
    (`BooleanFunctionTest.boolFnCapture, BooleanFunctionTest.boolFnCapture, false),
    (`BooleanFunctionTest.boolFnAnnotation, BooleanFunctionTest.boolFnAnnotation, false),
    (`BooleanFunctionTest.boolFnUnused, BooleanFunctionTest.boolFnUnused, false),
    (`BooleanFunctionTest.rangeBoolFnYield, BooleanFunctionTest.rangeBoolFnYield, true),
    (`BooleanFunctionTest.rangeBoolFnBreak, BooleanFunctionTest.rangeBoolFnBreak, true),
    (`BooleanFunctionTest.rangeBoolFnContinue, BooleanFunctionTest.rangeBoolFnContinue, true),
    (`BooleanFunctionTest.rangeBoolFnJoined, BooleanFunctionTest.rangeBoolFnJoined, true),
    (`BooleanFunctionTest.rangeBoolFnCapture, BooleanFunctionTest.rangeBoolFnCapture, true),
    (`BooleanFunctionTest.rangeBoolFnBounds, BooleanFunctionTest.rangeBoolFnBounds, true),
    (`BooleanFunctionTest.rangeBoolFnStep, BooleanFunctionTest.rangeBoolFnStep, true),
    (`BooleanFunctionTest.rangeBoolFnOuter, BooleanFunctionTest.rangeBoolFnOuter, true),
    (`BooleanFunctionTest.rangeResultFunctionBool, BooleanFunctionTest.rangeResultFunctionBool, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean function extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanFunctionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanFunctionTest.boolFnUnusedUnsupported, `BooleanFunctionTest.boolFnUnsupportedArgument, `BooleanFunctionTest.boolFnBooleanResult, `BooleanFunctionTest.rangeBoolFnUnusedUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean function accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let natType := Lean.Expr.const ``Nat []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.true []
  let make (input domain result body argument : Lean.Expr) := Lean.Expr.letE `f
    (.forallE `flag input result .default) (.lam `flag domain body .default)
    (.app (.bvar 0) argument) false
  for (result, body, isStep) in [(wordType, one, false),
      (LeanExe.Source.Scalar.Step.resultType .word, LeanExe.Source.Scalar.Step.yieldDirect one, true)] do
    let wrongWord := if isStep then LeanExe.Source.Scalar.Step.yieldDirect (.bvar 0) else .bvar 0
    for source in [make boolType wordType result body yes,
        make wordType boolType result body yes,
        make natType boolType result body yes,
        make boolType natType result body yes,
        make boolType boolType result wrongWord yes,
        make boolType boolType result body one] do
      let rejected := if isStep then (LeanExe.Extract.Core.extractScalarStepWith [] source).isNone
        else (LeanExe.Extract.Core.extractScalarExprWith [] source).isNone
      unless rejected do throwError "invalid Boolean helper accepted: {source}"
  Lean.logInfo "328 native/Boolean-function IR comparisons, four declaration rejection tests and twelve raw helper rejection tests passed"
