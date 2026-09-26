import LeanExe.Extract.ScalarFunc

namespace BooleanApplicationTest

def booleanApplyWord (x y : UInt64) : UInt64 :=
  if (fun z : UInt64 => z == y) x then x + 1 else y * 3

def booleanApplyBool (x y : UInt64) : UInt64 :=
  ((fun flag : Bool => !flag || x == y) (x != 0)).toUInt64 + y

def booleanApplyCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun z : UInt64 => z + y
  ((fun n : UInt64 => outer && f n == x) (x + y)).toUInt64

def booleanApplyNested (x y : UInt64) : UInt64 :=
  ((fun n : UInt64 =>
    (fun flag : Bool => flag && n != y) (n == x)) (x + y)).toUInt64 + x

def booleanApplyDependent (x y : UInt64) : UInt64 :=
  ((fun n : UInt64 => if _h : n < y then n != x else n == y) (x + 1)).toUInt64

def booleanApplyId (x y : UInt64) : UInt64 :=
  ((fun n : Id UInt64 =>
    (fun flag : Id Bool => !flag && !(@BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) n 0))
      (@BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) n y)) (x + y)).toUInt64

def booleanApplyUnused (x y : UInt64) : UInt64 :=
  ((fun _n : UInt64 => x != y) (x / y)).toUInt64

def booleanApplyDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure ((fun n : UInt64 => n == y) (x + 1))
  let next ← pure ((fun b : Bool => b || x != 0) flag)
  if next then return x + y else return x - y

def rangeBooleanApplyBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
    if (fun n : UInt64 => n % 7 == 0) a then break
  return a

def rangeBooleanApplyContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (fun flag : Bool => !flag) (UInt64.ofNat i % 3 == 0) then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeBooleanApplyCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let flag := (fun n : UInt64 =>
      (fun b : Bool => b && a != seed) (n % 7 == 0)) (UInt64.ofNat i)
    if flag then pure (.done (a + UInt64.ofNat i))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def hasApplication : Lean.Expr → Bool
  | .app (.lam ..) _ => true
  | .app f a => hasApplication f || hasApplication a
  | .lam _ type body _ | .forallE _ type body _ => hasApplication type || hasApplication body
  | .letE _ type value body _ => hasApplication type || hasApplication value || hasApplication body
  | .mdata _ body | .proj _ _ body => hasApplication body
  | _ => false

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanApplicationTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanApplicationTest.booleanApplyWord, BooleanApplicationTest.booleanApplyWord, false),
    (`BooleanApplicationTest.booleanApplyBool, BooleanApplicationTest.booleanApplyBool, false),
    (`BooleanApplicationTest.booleanApplyCapture, BooleanApplicationTest.booleanApplyCapture, false),
    (`BooleanApplicationTest.booleanApplyNested, BooleanApplicationTest.booleanApplyNested, false),
    (`BooleanApplicationTest.booleanApplyDependent, BooleanApplicationTest.booleanApplyDependent, false),
    (`BooleanApplicationTest.booleanApplyId, BooleanApplicationTest.booleanApplyId, false),
    (`BooleanApplicationTest.booleanApplyUnused, BooleanApplicationTest.booleanApplyUnused, false),
    (`BooleanApplicationTest.booleanApplyDo, BooleanApplicationTest.booleanApplyDo, false),
    (`BooleanApplicationTest.rangeBooleanApplyBreak, BooleanApplicationTest.rangeBooleanApplyBreak, true),
    (`BooleanApplicationTest.rangeBooleanApplyContinue, BooleanApplicationTest.rangeBooleanApplyContinue, true),
    (`BooleanApplicationTest.rangeBooleanApplyCapture, BooleanApplicationTest.rangeBooleanApplyCapture, true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless BooleanApplicationTest.hasApplication value do
      throwError "{name}: source no longer contains a lambda application"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean application extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanApplicationTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 184 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-application IR comparisons passed"
