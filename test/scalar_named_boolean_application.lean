import LeanExe.Extract.ScalarFunc

namespace NamedBooleanTest

def namedBooleanWord (x y : UInt64) : UInt64 :=
  if (let f : UInt64 → Bool := fun n => n == y; f x) then x + 1 else y * 3

def namedBooleanBool (x y : UInt64) : UInt64 :=
  (let f : Bool → Bool := fun b => !b || x == y; f (x != 0)).toUInt64 + y

def namedBooleanCapture (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let shift := fun z : UInt64 => z + y
  (let f : UInt64 → Bool := fun n => outer && shift n == x; f (x + y)).toUInt64

def namedBooleanNested (x y : UInt64) : UInt64 :=
  (let f : UInt64 → Bool := fun n =>
     let g : Bool → Bool := fun b => b && n != y
     g (n == x)
   f (x + y)).toUInt64 + x

def namedBooleanDependent (x y : UInt64) : UInt64 :=
  (let f : UInt64 → Bool := fun n => if _h : n < y then n != x else n == y
   f (x + 1)).toUInt64

def namedBooleanId (x y : UInt64) : UInt64 :=
  (let f : Id UInt64 → Id Bool := fun n =>
     let g : Id Bool → Id Bool := fun b => !b &&
       !(@BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) n 0)
     g (@BEq.beq UInt64 (@instBEqOfDecidableEq UInt64 instDecidableEqUInt64) n y)
   f (x + y)).toUInt64

def namedBooleanUnused (x y : UInt64) : UInt64 :=
  (let f : UInt64 → Bool := fun _n => x != y; f (x / y)).toUInt64

def namedBooleanDo (x y : UInt64) : UInt64 := Id.run do
  let flag ← pure (let f : UInt64 → Bool := fun n => n == y; f (x + 1))
  let next ← pure (let g : Bool → Bool := fun b => b || x != 0; g flag)
  if next then return x + y else return x - y

def rangeNamedBooleanBreak (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + UInt64.ofNat i
    if (let f : UInt64 → Bool := fun n => n % 7 == 0; f a) then break
  return a

def rangeNamedBooleanContinue (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f : Bool → Bool := fun b => !b; f (UInt64.ofNat i % 3 == 0)) then continue
    a := a + UInt64.ofNat i + 1
  return a

def rangeNamedBooleanCapture (count seed : UInt64) : UInt64 :=
  forIn (m := Id) [:count.toNat] seed fun i a =>
    let flag :=
      let f : UInt64 → Bool := fun n =>
        let g : Bool → Bool := fun b => b && a != seed
        g (n % 7 == 0)
      f (UInt64.ofNat i)
    if flag then pure (.done (a + UInt64.ofNat i))
    else pure (.yield (a * 3 + UInt64.ofNat i))

def hasNamedApplication : Lean.Expr → Bool
  | .letE _ (.forallE ..) (.lam ..) (.app (.bvar 0) _) _ => true
  | .app f a => hasNamedApplication f || hasNamedApplication a
  | .lam _ type body _ | .forallE _ type body _ => hasNamedApplication type || hasNamedApplication body
  | .letE _ type value body _ => hasNamedApplication type || hasNamedApplication value || hasNamedApplication body
  | .mdata _ body | .proj _ _ body => hasNamedApplication body
  | _ => false

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end NamedBooleanTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`NamedBooleanTest.namedBooleanWord, NamedBooleanTest.namedBooleanWord, false),
    (`NamedBooleanTest.namedBooleanBool, NamedBooleanTest.namedBooleanBool, false),
    (`NamedBooleanTest.namedBooleanCapture, NamedBooleanTest.namedBooleanCapture, false),
    (`NamedBooleanTest.namedBooleanNested, NamedBooleanTest.namedBooleanNested, false),
    (`NamedBooleanTest.namedBooleanDependent, NamedBooleanTest.namedBooleanDependent, false),
    (`NamedBooleanTest.namedBooleanId, NamedBooleanTest.namedBooleanId, false),
    (`NamedBooleanTest.namedBooleanUnused, NamedBooleanTest.namedBooleanUnused, false),
    (`NamedBooleanTest.namedBooleanDo, NamedBooleanTest.namedBooleanDo, false),
    (`NamedBooleanTest.rangeNamedBooleanBreak, NamedBooleanTest.rangeNamedBooleanBreak, true),
    (`NamedBooleanTest.rangeNamedBooleanContinue, NamedBooleanTest.rangeNamedBooleanContinue, true),
    (`NamedBooleanTest.rangeNamedBooleanCapture, NamedBooleanTest.rangeNamedBooleanCapture, true)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    unless NamedBooleanTest.hasNamedApplication value do
      throwError "{name}: source no longer contains a named helper application"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: named Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else NamedBooleanTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 184 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/named-Boolean IR comparisons passed"
