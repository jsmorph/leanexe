import LeanExe.Extract.ScalarFunc

namespace BooleanLetTest

def boolLetNested (x y : UInt64) : UInt64 :=
  (let flag := x == 0; flag && y != 0).toUInt64 + x

def boolLetCapture (x y : UInt64) : UInt64 :=
  let outer := x == 0
  let flag := (let localFlag := y == 0; ((if localFlag then x else y) == x) || outer)
  flag.toUInt64 + y

def boolLetShadow (x y : UInt64) : UInt64 :=
  let a := x != 0
  (let a := a; let a := !a; a != false).toUInt64 + y

def boolLetUnused (x y : UInt64) : UInt64 :=
  (let _unused := x == y; y != 0).toUInt64

def boolLetDependent (x y : UInt64) : UInt64 :=
  (let flag := if _h : x < y then x == 0 else y != 0
   let other := x != y
   if _h : flag = other then !flag else decide (flag ≠ other)).toUInt64 + x

def boolLetHelper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    (let a := flag
     let b := outer
     (let g := fun z : UInt64 => if a then z + x else z + y; g y) == x || b).toUInt64
  f (y != 0) + x

def boolLetDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (let inside := x == 0; inside || y == 0)
  let other ← if flag then pure (let inside := y != 0; !inside) else pure (let inside := x != 0; inside)
  let mut z := x
  if (let same := flag == other; same) then z := z + y else z := z - y
  return z + (let answer := decide (flag ≠ other); answer).toUInt64

def boolLetNegated (x y : UInt64) : UInt64 :=
  let outside := y == 0
  (!(let inside := x == 0; inside == outside)).toUInt64 +
    (!!(let inside := outside; inside || x != 0)).toUInt64

def rangeBoolLetYield (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag ← pure (let even := a % 2 == 0; (if even then a else UInt64.ofNat i) != seed)
    a := a + flag.toUInt64 + UInt64.ofNat i
    if flag then break
  return a

def rangeBoolLetJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let even ← pure (let flag := a % 2 == 0; flag)
    let next ← if even then pure (let flag := UInt64.ofNat i == 0; !flag) else pure (let flag := a == seed; flag)
    if next then a := a + 2 else a := a + 5
    if (let flag := a % 7 == 0; flag != next) then break
  return a

def rangeBoolLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let skip := UInt64.ofNat i % 3 == 1; skip && a != 0) then continue
    a := a + UInt64.ofNat i
    if (let stop := a % 7 == 0; if _h : stop then a != seed else false) then break
  return a

def rangeBoolLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer := seed != 0
  let f := fun flag : Bool => (let saved := outer; saved != flag).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g := fun flag : Bool => f (let saved := flag; saved || outer) + a
    a := g (let even := UInt64.ofNat i % 2 == 0; even)
    if (let saved := a % 11 == 0; saved != outer) then break
  return a + f (let saved := a == 0; saved)

def rangeBoolLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let first := (let flag := seed == 0; !flag).toUInt64
  let stop := count + (let flag := seed != 0; flag).toUInt64
  let mut a := seed
  for i in [first.toNat:stop.toNat:2] do
    a := a + (let flag := UInt64.ofNat i % 2 == 0; if flag then a == seed else !flag).toUInt64
    if (let flag := a % 7 == 0; flag) then break
  return a

def rangeBoolLetStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let outer := a == seed
    let f : Bool → Id (ForInStep UInt64) := fun flag => do
      let next ← pure (let localFlag := flag; localFlag != outer)
      if _h : next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (let localFlag := next; !localFlag).toUInt64)
    f (let even := UInt64.ofNat i % 2 == 0; even)

def rangeBoolLetOuter (count seed : UInt64) : UInt64 := Id.run do
  let flag ← pure (let positive := count != 0; positive)
  let mut a := seed + (let localFlag := flag; !localFlag).toUInt64
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i + 1
    if (let stop := a % 7 == 0; stop != flag) then break
  let changed ← pure (let same := a == seed; same != flag)
  return a + (let answer := changed; answer || flag).toUInt64

def rangeBoolLetUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let flag := a == seed
    let _unused := (let inner := UInt64.ofNat i == 0; !inner || flag)
    a := a + UInt64.ofNat i + 1
    if flag then break
  return a

def boolLetUnsupportedBound (x y : UInt64) : UInt64 :=
  (let _unused := toString x == toString y; true).toUInt64

def boolLetUnsupportedBody (x y : UInt64) : UInt64 :=
  let _unused := (let flag := x == 0; if flag then true else toString x == toString y)
  x + y

def boolWordLetOriginal (x y : UInt64) : UInt64 :=
  (let word := x + y; word == 0).toUInt64

def rangeBoolLetUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _unused := (let _flag := toString a == toString seed; false)
    return .yield (a + 1)
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanLetTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanLetTest.boolLetNested, BooleanLetTest.boolLetNested, false),
    (`BooleanLetTest.boolLetCapture, BooleanLetTest.boolLetCapture, false),
    (`BooleanLetTest.boolLetShadow, BooleanLetTest.boolLetShadow, false),
    (`BooleanLetTest.boolLetUnused, BooleanLetTest.boolLetUnused, false),
    (`BooleanLetTest.boolLetDependent, BooleanLetTest.boolLetDependent, false),
    (`BooleanLetTest.boolLetHelper, BooleanLetTest.boolLetHelper, false),
    (`BooleanLetTest.boolLetDo, BooleanLetTest.boolLetDo, false),
    (`BooleanLetTest.boolLetNegated, BooleanLetTest.boolLetNegated, false),
    (`BooleanLetTest.boolWordLetOriginal, BooleanLetTest.boolWordLetOriginal, false),
    (`BooleanLetTest.rangeBoolLetYield, BooleanLetTest.rangeBoolLetYield, true),
    (`BooleanLetTest.rangeBoolLetJoined, BooleanLetTest.rangeBoolLetJoined, true),
    (`BooleanLetTest.rangeBoolLetContinue, BooleanLetTest.rangeBoolLetContinue, true),
    (`BooleanLetTest.rangeBoolLetCapture, BooleanLetTest.rangeBoolLetCapture, true),
    (`BooleanLetTest.rangeBoolLetBounds, BooleanLetTest.rangeBoolLetBounds, true),
    (`BooleanLetTest.rangeBoolLetStep, BooleanLetTest.rangeBoolLetStep, true),
    (`BooleanLetTest.rangeBoolLetOuter, BooleanLetTest.rangeBoolLetOuter, true),
    (`BooleanLetTest.rangeBoolLetUnused, BooleanLetTest.rangeBoolLetUnused, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean let extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanLetTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`BooleanLetTest.boolLetUnsupportedBound, `BooleanLetTest.boolLetUnsupportedBody, `BooleanLetTest.rangeBoolLetUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Boolean let accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.true []
  let scalarLocals : List LeanExe.Extract.Core.ScalarBinding := [.boolean (.u64 1), .word (.u64 9)]
  let stepLocals : List LeanExe.Extract.Core.ScalarStepBinding := [.scalar (.boolean (.u64 1)), .scalar (.word (.u64 9))]
  let mut rawRejections : Nat := 0
  for nondep in [false, true] do
    let make (type value body : Lean.Expr) := Lean.Expr.letE `flag type value body nondep
    let valid := make boolType (.bvar 0) (.bvar 0)
    unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals
        (.letE `unused boolType valid one false)).isSome do
      throwError "valid Boolean let rejected in scalar code"
    unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
        (.letE `unused boolType valid (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isSome do
      throwError "valid Boolean let rejected in step code"
    let wordValid := make wordType one yes
    unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals
        (.letE `unused boolType wordValid one false)).isSome do
      throwError "promoted word let rejected in scalar code"
    unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
        (.letE `unused boolType wordValid (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isSome do
      throwError "promoted word let rejected in step code"
    let invalid := [make boolType one yes, make boolType yes one,
      make (.const ``Bool [.zero]) yes yes,
      make boolType (.bvar 1) yes, make boolType yes (.bvar 2),
      make boolType (.bvar 7) yes, make boolType yes (.bvar 7),
      make boolType yes (make boolType one yes),
      make boolType yes (LeanExe.Source.Scalar.BooleanComparison.eq.expr (.bvar 0) one)]
    for argument in invalid do
      unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals
          (.letE `unused boolType argument one false)).isNone do
        throwError "invalid Boolean let accepted in scalar code"
      rawRejections := rawRejections + 1
      unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
          (.letE `unused boolType argument (LeanExe.Source.Scalar.Step.yieldDirect one) false)).isNone do
        throwError "invalid Boolean let accepted in step code"
      rawRejections := rawRejections + 1
  Lean.logInfo m!"318 native/Boolean-let IR comparisons, three declaration rejection tests and {rawRejections} raw let rejection tests passed"
