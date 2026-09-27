import LeanExe.Extract.ScalarFunc

namespace BooleanBindTest

def boolBindLet (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x == y)
  return if flag then x + y * 3 else x - y * 5

def boolBindAlias (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x != y)
  let alias ← pure flag
  let inverted ← pure (!!!alias)
  return if inverted then ~~~x else ~~~y

def boolBindWrapped (x y : UInt64) : UInt64 := Id.run do
  let flag ← Id.run (pure (x == y))
  let alias ← pure (Id.run (pure flag))
  return if alias && !(x == 0) then x + 7 else y - 11

def boolBindShadow (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x != y)
  let f := fun a b : UInt64 => if flag then a + b else a - b
  let flag ← pure (y == 0)
  return if flag then f x y else f y x

def boolBindCapture (x y : UInt64) : UInt64 := Id.run do
  let outer ← pure (x == 0)
  let f : UInt64 → UInt64 → UInt64 → Id UInt64 := fun a b c => do
    let inner ← pure (a == b || b == c)
    return if outer || !inner then a + b * 3 - c else a - b + c
  f x y (x + 7)

def boolBindDependent (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x == y)
  if _h : flag then
    let next ← pure (x == 0)
    return if next then y + 3 else x - 5
  else
    let next ← pure (x != 0 && y != 0)
    return if _k : next then x / y else y % x

def boolBindDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (x == y)
  let mut a := x
  if flag then a := a + y else a := a - y
  let next ← pure (a % 3 == 0)
  let z ← if next && !flag then pure (a * 7) else pure (a + 5)
  return z ^^^ y

def boolBindUnused (x y : UInt64) : UInt64 := Id.run do
  let _unused ← pure (true || x / 0 == y)
  let kept ← pure true
  return if kept then x + y else x - y

def rangeBoolBindYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (UInt64.ofNat i % 2 == 0)
    if even then a := a + 3 else a := a + 7
  return a

def rangeBoolBindBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop ← pure (a % 7 == 0 || UInt64.ofNat i == 12)
    if _h : stop then break
  return a

def rangeBoolBindContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip ← pure (UInt64.ofNat i % 3 == 1)
    if skip then continue
    a := a + UInt64.ofNat i
    let stop ← pure (a % 11 == 0)
    if stop && !skip then break
  return a

def rangeBoolBindJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (a % 2 == 0)
    if even then a := a + 2 else a := a + 5
    let next ← Id.run (pure (!even))
    let z ← if next then pure (a - 1) else pure (a + 3)
    a := z + UInt64.ofNat i
    let stop ← pure (a % 13 == 0)
    if stop then break
  return a

def rangeBoolBindCapture (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (seed % 3 == 0)
  let f := fun x y z : UInt64 => if flag then x + y - z else x - y + z
  let mut a := seed
  for i in [:count.toNat] do
    let inner ← pure (a % 5 == 0)
    a := f a (UInt64.ofNat i) count
    if inner && flag then break
  return a

def rangeBoolBindBounds (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (seed % 3 == 0)
  let first : UInt64 := if flag then 0 else 2
  let stop := if !flag && count != 0 then count - 1 else count
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    let finish ← pure (a % 7 == 0)
    if finish && flag then break
    a := a + UInt64.ofNat i
  return a

def rangeBoolBindStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let captured ← pure (a % 5 == 0)
    let f : UInt64 → UInt64 → UInt64 → Id (ForInStep UInt64) := fun x y z => do
      let inner ← pure (x == y || y == z)
      if _h : captured && inner then return .done (x + y - z)
      else return .yield (x - y + z)
    f a (UInt64.ofNat i) count

def rangeBoolBindOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (seed == 0)
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    let stop ← pure (a % 7 == 0)
    if stop && flag then break
  let changed ← pure (a != seed)
  return if changed then a + count else a - count

def boolBindCustomPure (x y : UInt64) : UInt64 := Id.run do
  let flag ← @Pure.pure Id ⟨fun value => value⟩ Bool (x == y)
  return if flag then x else y

def boolBindCustomBind (x y : UInt64) : UInt64 :=
  @Bind.bind Id ⟨fun value next => next value⟩ Bool UInt64 (pure (x == y))
    (fun flag => if flag then x else y)

def boolBindUnusedUnsupported (x y : UInt64) : UInt64 := Id.run do
  let _unused ← pure (toString x == toString y)
  return x + y

def rangeBoolBindUnusedUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused ← pure (toString a == toString seed)
    return .yield (a + 1)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanBindTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanBindTest.boolBindLet, BooleanBindTest.boolBindLet, false),
    (`BooleanBindTest.boolBindAlias, BooleanBindTest.boolBindAlias, false),
    (`BooleanBindTest.boolBindWrapped, BooleanBindTest.boolBindWrapped, false),
    (`BooleanBindTest.boolBindShadow, BooleanBindTest.boolBindShadow, false),
    (`BooleanBindTest.boolBindCapture, BooleanBindTest.boolBindCapture, false),
    (`BooleanBindTest.boolBindDependent, BooleanBindTest.boolBindDependent, false),
    (`BooleanBindTest.boolBindDo, BooleanBindTest.boolBindDo, false),
    (`BooleanBindTest.boolBindUnused, BooleanBindTest.boolBindUnused, false),
    (`BooleanBindTest.rangeBoolBindYield, BooleanBindTest.rangeBoolBindYield, true),
    (`BooleanBindTest.rangeBoolBindBreak, BooleanBindTest.rangeBoolBindBreak, true),
    (`BooleanBindTest.rangeBoolBindContinue, BooleanBindTest.rangeBoolBindContinue, true),
    (`BooleanBindTest.rangeBoolBindJoined, BooleanBindTest.rangeBoolBindJoined, true),
    (`BooleanBindTest.rangeBoolBindCapture, BooleanBindTest.rangeBoolBindCapture, true),
    (`BooleanBindTest.rangeBoolBindBounds, BooleanBindTest.rangeBoolBindBounds, true),
    (`BooleanBindTest.rangeBoolBindStep, BooleanBindTest.rangeBoolBindStep, true),
    (`BooleanBindTest.rangeBoolBindOuter, BooleanBindTest.rangeBoolBindOuter, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean bind extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanBindTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanBindTest.boolBindCustomPure, `BooleanBindTest.boolBindCustomBind, `BooleanBindTest.boolBindUnusedUnsupported, `BooleanBindTest.rangeBoolBindUnusedUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean bind accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let stepType := LeanExe.Source.Scalar.Step.resultType .word
  let one := LeanExe.Source.Scalar.literalExpr 1
  let step := LeanExe.Source.Scalar.Step.yieldDirect one
  let input := LeanExe.Source.Scalar.BooleanIdentity.pure (.const ``Bool.true [])
  let make (domain output value body : Lean.Expr) :=
    Lean.mkAppN (.const ``Bind.bind [.zero, .zero]) #[.const ``Id [.zero],
      .app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero])) (.const ``Id.instMonad [.zero]),
      boolType, output, value, .lam `flag domain body .default]
  for (domain, argument) in [(wordType, input),
      (boolType, LeanExe.Source.Scalar.Identity.pure one)] do
    unless (LeanExe.Extract.Core.extractScalarExprWith [] (make domain wordType argument one)).isNone do
      throwError "wrong scalar Boolean bind domain/action accepted"
    unless (LeanExe.Extract.Core.extractScalarStepWith [] (make domain stepType argument step)).isNone do
      throwError "wrong step Boolean bind domain/action accepted"
  unless (LeanExe.Extract.Core.extractScalarExprWith [] (make boolType wordType input (.bvar 0))).isNone do
    throwError "Boolean bound value accepted as a word"
  unless (LeanExe.Extract.Core.extractScalarStepWith []
      (make boolType stepType input (LeanExe.Source.Scalar.Step.yieldDirect (.bvar 0)))).isNone do
    throwError "Boolean bound value accepted as a step word"
  let decorated := Lean.Expr.mdata {} input
  unless (LeanExe.Extract.Core.extractScalarExprWith [] (make boolType wordType decorated one)).isSome do
    throwError "metadata-wrapped scalar Boolean action rejected"
  unless (LeanExe.Extract.Core.extractScalarStepWith [] (make boolType stepType decorated step)).isSome do
    throwError "metadata-wrapped step Boolean action rejected"
  Lean.logInfo "304 native/Boolean-bind IR comparisons, four declaration rejection tests, six raw bind rejection tests and two metadata tests passed"
