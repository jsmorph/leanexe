import LeanExe.Extract.ScalarFunc

namespace IdLetTest

def idLetWord (x y : UInt64) : UInt64 :=
  let value : Id UInt64 := x + y
  Id.run value + y

def idLetBoolean (x y : UInt64) : UInt64 :=
  let flag : Id Bool := x == 0
  if Id.run flag && y != 0 then x + y else x - y

def idLetLiteral (x y : UInt64) : UInt64 :=
  let value : Id (Id UInt64) := 3
  Id.run (Id.run value) + x + y

def idLetHelper (x y : UInt64) : UInt64 :=
  let f : Id (UInt64 → UInt64) := fun z => z + x
  f y

def idLetShadow (x y : UInt64) : UInt64 :=
  let value : Id (Id UInt64) := x + y
  let value : Id UInt64 := Id.run (Id.run value) * 3
  let flag : Id (Id Bool) := Id.run value == y
  if Id.run (Id.run flag) then Id.run value else x + y

def idLetOverflow (x y : UInt64) : UInt64 :=
  let value : Id (Id UInt64) := 18446744073709551619
  Id.run (Id.run value) + x + y

def idLetUnused (x y : UInt64) : UInt64 :=
  let _value : Id UInt64 := x / y
  let _flag : Id (Id Bool) := x == y
  x + y

def idLetDo (x y : UInt64) : UInt64 := Id.run do
  let flag : Id Bool := x != 0
  let value : Id (Id UInt64) := Id.run (pure (if Id.run flag then x + y else x - y))
  let saved ← pure (Id.run (Id.run value))
  let next : Id UInt64 := saved + y
  return Id.run next

def rangeIdLetYield (count seed : UInt64) : UInt64 := Id.run do
  let outer : Id Bool := seed != 0
  let mut a := seed
  for i in [:count.toNat] do
    let value : Id UInt64 := a + UInt64.ofNat i
    a := Id.run value + 1
    let stop : Id (Id Bool) := a % 7 == 0
    if Id.run (Id.run stop) && Id.run outer then break
  let value : Id UInt64 := a + seed
  return Id.run value

def rangeIdLetJoined (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let first : Id Bool := a % 2 == 0
    let next ← if Id.run first then pure (UInt64.ofNat i == 0) else pure (a != seed)
    let saved : Id (Id Bool) := next
    if Id.run (Id.run saved) then a := a + 2 else a := a + 5
    let stop : Id Bool := a % 7 == 0
    if Id.run stop && seed != 0 then break
  return a

def rangeIdLetContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let skip : Id (Id Bool) := UInt64.ofNat i % 3 == 1
    if Id.run (Id.run skip) && a != 0 then continue
    let value : Id UInt64 := a + UInt64.ofNat i
    a := Id.run value
    let stop : Id Bool := a % 7 == 0
    if Id.run stop && seed != 0 then break
  return a

def rangeIdLetCapture (count seed : UInt64) : UInt64 := Id.run do
  let outer : Id Bool := seed != 0
  let f : Id (Bool → UInt64) := fun flag => (flag && Id.run outer).toUInt64 + count
  let mut a := seed
  for i in [:count.toNat] do
    let g : Id (UInt64 → UInt64) := fun value => value + a
    a := g (f (UInt64.ofNat i % 2 == 0))
    let stop : Id (Id Bool) := a % 11 == 0
    if Id.run (Id.run stop) && Id.run outer then break
  return a + f (a == seed)

def rangeIdLetBounds (count seed : UInt64) : UInt64 := Id.run do
  let first : Id UInt64 := 1
  let stop : Id (Id UInt64) := count + (seed != 0).toUInt64
  let mut a := seed
  for i in [(Id.run first).toNat:(Id.run (Id.run stop)).toNat:2] do
    let delta : Id UInt64 := UInt64.ofNat i + 1
    a := a + Id.run delta
    let stop : Id Bool := a % 7 == 0
    if Id.run stop && seed != 0 then break
  return a

def rangeIdLetStep (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a => do
    let f : Id (Bool → Id (ForInStep UInt64)) := fun flag => do
      let next : Id Bool := flag && a != 0
      if _h : Id.run next then return .done (a + UInt64.ofNat i)
      else return .yield (a + (!flag).toUInt64)
    f (UInt64.ofNat i % 2 == 0)

def rangeIdLetOuter (count seed : UInt64) : UInt64 :=
  let initial : Id UInt64 := seed + 1
  let total : Id (Id UInt64) := Id.run do
    let mut a := Id.run initial
    for i in [:count.toNat] do
      a := a + UInt64.ofNat i + 1
      let stop : Id Bool := a % 7 == 0
      if Id.run stop && seed != 0 then break
    return a
  Id.run (Id.run total) + seed

def rangeIdLetUnused (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused : Id UInt64 := a / UInt64.ofNat i
    let _flag : Id (Id Bool) := a == seed
    a := a + UInt64.ofNat i + 1
    let stop : Id Bool := a % 7 == 0
    if Id.run stop && seed != 0 then break
  return a

def idLetUnsupportedBound (x y : UInt64) : UInt64 :=
  let _value : Id UInt64 := UInt64.ofNat (toString x).length
  x + y

def idLetUnsupportedBoolean (x y : UInt64) : UInt64 :=
  let _flag : Id Bool := toString x == toString y
  x + y

def idLetUnsupportedType (x y : UInt64) : UInt64 :=
  let _text : Id String := toString x
  x + y

def rangeIdLetUnsupported (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun _ a => do
    let _flag : Id Bool := toString a == toString seed
    return .yield (a + 1)
def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end IdLetTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`IdLetTest.idLetWord, IdLetTest.idLetWord, false),
    (`IdLetTest.idLetBoolean, IdLetTest.idLetBoolean, false),
    (`IdLetTest.idLetLiteral, IdLetTest.idLetLiteral, false),
    (`IdLetTest.idLetHelper, IdLetTest.idLetHelper, false),
    (`IdLetTest.idLetShadow, IdLetTest.idLetShadow, false),
    (`IdLetTest.idLetOverflow, IdLetTest.idLetOverflow, false),
    (`IdLetTest.idLetUnused, IdLetTest.idLetUnused, false),
    (`IdLetTest.idLetDo, IdLetTest.idLetDo, false),
    (`IdLetTest.rangeIdLetYield, IdLetTest.rangeIdLetYield, true),
    (`IdLetTest.rangeIdLetJoined, IdLetTest.rangeIdLetJoined, true),
    (`IdLetTest.rangeIdLetContinue, IdLetTest.rangeIdLetContinue, true),
    (`IdLetTest.rangeIdLetCapture, IdLetTest.rangeIdLetCapture, true),
    (`IdLetTest.rangeIdLetBounds, IdLetTest.rangeIdLetBounds, true),
    (`IdLetTest.rangeIdLetStep, IdLetTest.rangeIdLetStep, true),
    (`IdLetTest.rangeIdLetOuter, IdLetTest.rangeIdLetOuter, true),
    (`IdLetTest.rangeIdLetUnused, IdLetTest.rangeIdLetUnused, true)]
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Id-annotated let extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else IdLetTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
  for name in [`IdLetTest.idLetUnsupportedBound, `IdLetTest.idLetUnsupportedBoolean, `IdLetTest.idLetUnsupportedType, `IdLetTest.rangeIdLetUnsupported] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless (LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isNone do
      throwError "{name}: unsupported Id-annotated let accepted"
  let boolType := Lean.Expr.const ``Bool []
  let wordType := Lean.Expr.const ``UInt64 []
  let one := LeanExe.Source.Scalar.literalExpr 1
  let yes := Lean.Expr.const ``Bool.true []
  let scalarLocals : List LeanExe.Extract.Core.ScalarBinding := [.boolean (.u64 1), .word (.u64 9)]
  let stepLocals : List LeanExe.Extract.Core.ScalarStepBinding := [.scalar (.boolean (.u64 1)), .scalar (.word (.u64 9))]
  let identity (depth : Nat) (base : Lean.Expr) :=
    (List.range depth).foldl (fun type _ => Lean.mkApp (.const ``Id [.zero]) type) base
  let mut rawRejections : Nat := 0
  for depth in [1, 3] do
    let boolean := identity depth boolType
    let word := identity depth wordType
    for nondep in [false, true] do
      let make (type value body : Lean.Expr) := Lean.Expr.letE `annotated type value body nondep
      for (type, value) in [(boolean, .bvar 0), (word, .bvar 1), (boolean, yes), (word, one)] do
        unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals (make type value one)).isSome do
          throwError "valid Id let rejected in scalar code"
        unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
            (make type value (LeanExe.Source.Scalar.Step.yieldDirect one))).isSome do
          throwError "valid Id let rejected in step code"
      let invalid := [(.app (.const ``Id [.succ .zero]) boolType, yes),
        (.const ``Id [.zero], one), (identity depth (.const ``Nat []), one),
        (identity depth (.const ``String []), one), (word, yes), (boolean, one),
        (boolean, .bvar 1), (word, .bvar 0)]
      for (type, value) in invalid do
        unless (LeanExe.Extract.Core.extractScalarExprWith scalarLocals (make type value one)).isNone do
          throwError "invalid Id let accepted in scalar code"
        rawRejections := rawRejections + 1
        unless (LeanExe.Extract.Core.extractScalarStepWith stepLocals
            (make type value (LeanExe.Source.Scalar.Step.yieldDirect one))).isNone do
          throwError "invalid Id let accepted in step code"
        rawRejections := rawRejections + 1
  let evidence (depth number : Nat) (base : Lean.Expr) := Id.run do
    let mut type := LeanExe.Source.Scalar.ResultType.word
    let mut instance_ := base
    for _ in List.range depth do
      instance_ := Lean.mkApp3 (.const ``Id.instOfNat [.zero]) type.expr (.lit (.natVal number)) instance_
      type := .identity type
    return (type, instance_)
  let standard (number : Nat) := Lean.mkApp (.const ``UInt64.instOfNat []) (.lit (.natVal number))
  let head (type : Lean.Expr) (number : Nat) (instance_ : Lean.Expr) :=
    Lean.mkApp3 (.const ``OfNat.ofNat [.zero]) type (.lit (.natVal number)) instance_
  let mut numeralComparisons : Nat := 0
  for depth in [0, 1, 3] do
    for number in [0, 1, 18446744073709551615, 18446744073709551616,
        18446744073709551617, 340282366920938463463374607431768211473] do
      let (type, instance_) := evidence depth number (standard number)
      let some func := LeanExe.Extract.Core.extractScalarFunc `typedNumeral (some "entry")
          wordType (head type.expr number instance_) | throwError "valid typed numeral rejected"
      let module_ : LeanExe.IR.Module := { funcs := #[func] }
      unless module_.evalFunc 0 [] == UInt64.ofNat number do
        throwError "typed numeral native/IR mismatch for depth {depth}, number {number}"
      numeralComparisons := numeralComparisons + 1
  for depth in [1, 3] do
    for number in [0, 18446744073709551619] do
      let (type, instance_) := evidence depth number (standard number)
      let (inner, innerEvidence) := evidence (depth - 1) number (standard number)
      let (_, extraEvidence) := evidence (depth + 1) number (standard number)
      let (_, badBase) := evidence depth number
        (Lean.mkApp (.const ``UInt64.instOfNat [.zero]) (.lit (.natVal number)))
      let idInstance (levels : List Lean.Level) (sourceType : Lean.Expr) (n : Nat) :=
        Lean.mkApp3 (.const ``Id.instOfNat levels) sourceType (.lit (.natVal n)) innerEvidence
      let invalid := [head boolType number instance_,
        head (.app (.const ``Id [.succ .zero]) inner.expr) number instance_,
        Lean.mkApp3 (.const ``OfNat.ofNat [.succ .zero]) type.expr (.lit (.natVal number)) instance_,
        head type.expr number (idInstance [.zero] (.const ``Nat []) number),
        head type.expr number (idInstance [.zero] inner.expr (number + 1)),
        head type.expr number innerEvidence, head type.expr number extraEvidence,
        head type.expr number (.const `notTheStandardInstance []),
        head type.expr number (idInstance [.succ .zero] inner.expr number),
        head type.expr number badBase]
      for value in invalid do
        unless (LeanExe.Extract.Core.extractScalarExprWith [] value).isNone do
          throwError "malformed typed numeral accepted in scalar code"
        rawRejections := rawRejections + 1
        unless (LeanExe.Extract.Core.extractScalarStepWith []
            (LeanExe.Source.Scalar.Step.yieldDirect value)).isNone do
          throwError "malformed typed numeral accepted in step code"
        rawRejections := rawRejections + 1
  unless rawRejections == 144 && numeralComparisons == 18 do
    throwError "unexpected raw/numeral test counts: {rawRejections}, {numeralComparisons}"
  Lean.logInfo m!"304 native/Id-let IR comparisons, {numeralComparisons} native/typed-numeral IR comparisons, four declaration rejection tests and {rawRejections} raw rejection tests passed"
