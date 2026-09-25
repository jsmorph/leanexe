import LeanExe.Extract.ScalarFunc

namespace BooleanNestedIdTest

def nestedIdOperators (x y : UInt64) : UInt64 :=
  (Id.run (pure (x == 0)) && Id.run (pure (y != 0))).toUInt64 + x

def nestedIdBinding (x y : UInt64) : UInt64 :=
  (let flag : Id Bool := x == 0; Id.run flag || y != 0).toUInt64 + y

def nestedIdNested (x y : UInt64) : UInt64 :=
  (!(Id.run (pure (Id.run (pure (x == y)))) &&
    (let saved : Id (Id Bool) := x != 0; Id.run (Id.run saved)))).toUInt64 + x

def nestedIdHelper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    (Id.run (pure flag) && (let saved : Id Bool := outer; Id.run saved)).toUInt64 + x
  f (Id.run (pure (y == 0)))

def nestedIdDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (Id.run (pure (x == 0)) && y != 0)
  let next ← if flag then pure (Id.run (pure (x != y)) || flag)
    else pure (!(Id.run (pure (y == 0))))
  return x + (Id.run (pure next) && !flag).toUInt64

def nestedIdDependent (x y : UInt64) : UInt64 :=
  (if _h : Id.run (pure (x == 0)) && y != 0 then
    Id.run (pure (y == 1)) || x == y
   else Id.run (pure (x != y)) && y == 0).toUInt64 + x

def nestedIdUnused (x y : UInt64) : UInt64 :=
  (let _flag := Id.run (pure (x == y)) && x != 0
   Id.run (pure (x != y)) || y == 0).toUInt64 + x

def nestedIdShadow (x y : UInt64) : UInt64 :=
  (let flag : Id Bool := x == 0
   let flag : Id (Id Bool) := pure (Id.run flag && y != 0)
   Id.run (Id.run flag) || x == y).toUInt64 + y

def rangeNestedIdYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let stop := Id.run (pure (let value : Id Bool := (a + UInt64.ofNat i) % 7 == 0
                            Id.run value && Id.run (pure (seed != 0))))
    a := a + UInt64.ofNat i + 1
    if stop then break
  return a

def rangeNestedIdJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first ← pure (Id.run (pure (a % 2 == 0)) && seed != 0)
    let next ← if first then pure (Id.run (pure (UInt64.ofNat i == 0)) || a == seed)
      else pure (Id.run (pure (a != seed)) && !first)
    if next then a := a + 2 else a := a + 5
    if Id.run (pure (a % 7 == 0)) && seed != 0 then break
  return a

def rangeNestedIdContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if Id.run (pure (UInt64.ofNat i % 3 == 1)) && a != 0 then continue
    a := a + UInt64.ofNat i
    if Id.run (pure (a % 7 == 0)) && seed != 0 then break
  return a

def rangeNestedIdCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (Id.run (pure flag) && outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (Id.run (pure flag) || a == seed) + a
    a := g (Id.run (pure (UInt64.ofNat i % 2 == 0)) && outer)
    if Id.run (pure (a % 11 == 0)) && outer then break
  return a + f (Id.run (pure (a == seed)) || !outer)

def rangeNestedIdBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := (Id.run (pure (seed != 0)) && count != 0).toUInt64
  let stop := count + (Id.run (pure (count != 0)) || seed == 0).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    a := a + (Id.run (pure (UInt64.ofNat i % 2 == 0)) && a != 0).toUInt64
    if Id.run (pure (a % 7 == 0)) && seed != 0 then break
  return a

def rangeNestedIdStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (Id.run (pure flag) && a != 0)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (Id.run (pure (!next)) || flag).toUInt64)
    f (Id.run (pure (UInt64.ofNat i % 2 == 0)) && seed != 0)

def rangeNestedIdOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (Id.run (pure (count != 0)) && seed != 0)
  let mut a := seed + (Id.run (pure flag) || count == 0).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if Id.run (pure (a % 7 == 0)) && flag then break
  let changed ← pure (Id.run (pure (a != seed)) && flag)
  return a + (Id.run (pure changed) || !flag).toUInt64

def rangeNestedIdUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := Id.run (pure (a == seed)) && UInt64.ofNat i != 0
    a := a + UInt64.ofNat i + 1
    if Id.run (pure (a % 7 == 0)) && seed != 0 then break
  return a

def nestedIdUnsupportedBound (x y : UInt64) : UInt64 :=
  (let _flag := Id.run (pure (toString x == toString y)) && x != 0; true).toUInt64

def nestedIdUnsupportedBody (x y : UInt64) : UInt64 :=
  (Id.run (pure (toString x == toString y)) || x == 0).toUInt64

def nestedIdUnsupportedType (x y : UInt64) : UInt64 :=
  (Id.run (pure x.toNat) == y.toNat).toUInt64

def rangeNestedIdUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := Id.run (pure (toString a == toString seed)) && a != 0
    return .yield (a + 1)
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanNestedIdTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanNestedIdTest.nestedIdOperators, BooleanNestedIdTest.nestedIdOperators, false),
    (`BooleanNestedIdTest.nestedIdBinding, BooleanNestedIdTest.nestedIdBinding, false),
    (`BooleanNestedIdTest.nestedIdNested, BooleanNestedIdTest.nestedIdNested, false),
    (`BooleanNestedIdTest.nestedIdHelper, BooleanNestedIdTest.nestedIdHelper, false),
    (`BooleanNestedIdTest.nestedIdDo, BooleanNestedIdTest.nestedIdDo, false),
    (`BooleanNestedIdTest.nestedIdDependent, BooleanNestedIdTest.nestedIdDependent, false),
    (`BooleanNestedIdTest.nestedIdUnused, BooleanNestedIdTest.nestedIdUnused, false),
    (`BooleanNestedIdTest.nestedIdShadow, BooleanNestedIdTest.nestedIdShadow, false),
    (`BooleanNestedIdTest.rangeNestedIdYield, BooleanNestedIdTest.rangeNestedIdYield, true),
    (`BooleanNestedIdTest.rangeNestedIdJoined, BooleanNestedIdTest.rangeNestedIdJoined, true),
    (`BooleanNestedIdTest.rangeNestedIdContinue, BooleanNestedIdTest.rangeNestedIdContinue, true),
    (`BooleanNestedIdTest.rangeNestedIdCapture, BooleanNestedIdTest.rangeNestedIdCapture, true),
    (`BooleanNestedIdTest.rangeNestedIdBounds, BooleanNestedIdTest.rangeNestedIdBounds, true),
    (`BooleanNestedIdTest.rangeNestedIdStep, BooleanNestedIdTest.rangeNestedIdStep, true),
    (`BooleanNestedIdTest.rangeNestedIdOuter, BooleanNestedIdTest.rangeNestedIdOuter, true),
    (`BooleanNestedIdTest.rangeNestedIdUnused, BooleanNestedIdTest.rangeNestedIdUnused, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: nested Boolean Id operation extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanNestedIdTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanNestedIdTest.nestedIdUnsupportedBound, `BooleanNestedIdTest.nestedIdUnsupportedBody, `BooleanNestedIdTest.nestedIdUnsupportedType, `BooleanNestedIdTest.rangeNestedIdUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported nested Boolean Id operation accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.true []
  let scalarLocals : List LeanExe.Extract.Core.ScalarBinding := [.boolean (.u64 1), .word (.u64 9)]
  let stepLocals : List LeanExe.Extract.Core.ScalarStepBinding := [.scalar (.boolean (.u64 1)), .scalar (.word (.u64 9))]
  let identity (depth : Nat) (base : Lean.Expr) :=
    (List.range depth).foldl (fun type _ => Lean.mkApp (.const ``Id [.zero]) type) base
  let runType (type body : Lean.Expr) := Lean.mkApp2 (.const ``Id.run [.zero]) type body
  let pureType (type body : Lean.Expr) :=
    Lean.mkAppN (.const ``Pure.pure [.zero, .zero]) #[.const ``Id [.zero],
      .app (.app (.const ``Applicative.toPure [.zero, .zero]) (.const ``Id [.zero]))
        (.app (.app (.const ``Monad.toApplicative [.zero, .zero]) (.const ``Id [.zero]))
          (.const ``Id.instMonad [.zero])), type, body]
  let mut rawRejections : Nat := 0
  for depth in [0, 2] do
    let type := identity depth boolType
    for isPure in [false, true] do
      let make := if isPure then pureType else runType
      for negations in [0, 1] do
        let frame (body : Lean.Expr) := Lean.mkApp2 (.const ``Bool.and []) yes
          (LeanExe.Source.Scalar.BooleanGuardNegation.expr negations (.mdata default body))
        let comparison := LeanExe.Source.Scalar.BooleanComparison.eq.expr (.bvar 1) one
        for value in [make type (.bvar 0), make type comparison,
            .mdata default (make type (.bvar 0)), make type (.mdata default (.bvar 0))] do
          let argument := frame value
          let some parsed := LeanExe.Extract.Core.booleanLocalOperands? argument |
            throwError "nested Boolean wrapper syntax rejected"
          unless parsed.expr == argument do
            throwError "Boolean wrapper syntax or metadata changed"
          unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals
              (.letE `unused boolType argument one false)).isSome do
            throwError "valid nested Boolean wrapper rejected in scalar code"
          unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
              (.letE `unused boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isSome do
            throwError "valid nested Boolean wrapper rejected in step code"
        let badTypes := [wordType, .const ``Nat [], .const ``Id [.zero],
          .const ``Bool [.zero], .app (.const ``Id [.succ .zero]) boolType,
          identity (depth + 1) (.const ``Nat [])]
        let badHead := if isPure then
            Lean.mkAppN (.const ``Pure.pure [.zero, .zero]) #[.const ``Id [.zero],
              .const `notTheStandardInstance [], type, yes]
          else Lean.mkApp2 (.const ``Id.run [.succ .zero]) type yes
        let invalid := badTypes.map (fun bad => make bad yes) ++
          [make type one, make type (.bvar 1), badHead,
           .letE `word wordType one (make type (.bvar 0)) false]
        for value in invalid do
          let argument := frame value
          unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals
              (.letE `unused boolType argument one false)).isNone do
            throwError "invalid nested wrapper accepted in scalar code"
          rawRejections := rawRejections + 1
          unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
              (.letE `unused boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isNone do
            throwError "invalid nested wrapper accepted in step code"
          rawRejections := rawRejections + 1
  unless rawRejections == 160 do throwError "unexpected raw wrapper test count: {rawRejections}"
  Lean.logInfo m!"304 native/Boolean-nested-Id IR comparisons, four declaration rejection tests and {rawRejections} raw wrapper rejection tests passed"
