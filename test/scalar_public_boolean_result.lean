import LeanExe.Extract.ScalarFunc

namespace PublicBooleanResultTest

def publicBooleanTrue (_x _y : UInt64) : Bool := true

def publicBooleanCompare (x y : UInt64) : Bool := x != y && x + 1 == y

def publicBooleanChoice (x y : UInt64) : Bool :=
  if x < y then x / y == 0 else !(y % x == 0)

def publicBooleanDependent (x y : UInt64) : Bool :=
  if _h : x == y then x != 0 else y != 0

def publicBooleanLet (x y : UInt64) : Bool :=
  let n := x + y
  let flag := n == 0
  let other := flag || x < y
  other && !(n == y)

def publicBooleanDo (x y : UInt64) : Bool := Id.run do
  let n ← pure (x + y)
  let flag ← pure (n == 0)
  return flag || y == 0

def publicBooleanNamed (x y : UInt64) : Bool :=
  let f : UInt64 → Bool := fun n => n != y
  f (x + 1)

def publicBooleanCaptured (x y : UInt64) : Bool :=
  let flag := x == 0
  (fun b : Bool => b || flag) (y == 0)

def publicBooleanDecision (x y : UInt64) : Bool :=
  decide ((let b := x == y; b ∨ x < y) ∧ ¬ (y == 0))

def publicBooleanWrapped (x y : UInt64) : Bool :=
  Id.run (pure (Id.run (pure ((x == y) != (x == 0)))))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PublicBooleanResultTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PublicBooleanResultTest.publicBooleanTrue, (fun x y => (PublicBooleanResultTest.publicBooleanTrue x y).toUInt64), false),
    (`PublicBooleanResultTest.publicBooleanCompare, (fun x y => (PublicBooleanResultTest.publicBooleanCompare x y).toUInt64), false),
    (`PublicBooleanResultTest.publicBooleanChoice, (fun x y => (PublicBooleanResultTest.publicBooleanChoice x y).toUInt64), false),
    (`PublicBooleanResultTest.publicBooleanDependent, (fun x y => (PublicBooleanResultTest.publicBooleanDependent x y).toUInt64), false),
    (`PublicBooleanResultTest.publicBooleanLet, (fun x y => (PublicBooleanResultTest.publicBooleanLet x y).toUInt64), false),
    (`PublicBooleanResultTest.publicBooleanDo, (fun x y => (PublicBooleanResultTest.publicBooleanDo x y).toUInt64), false),
    (`PublicBooleanResultTest.publicBooleanNamed, (fun x y => (PublicBooleanResultTest.publicBooleanNamed x y).toUInt64), false),
    (`PublicBooleanResultTest.publicBooleanCaptured, (fun x y => (PublicBooleanResultTest.publicBooleanCaptured x y).toUInt64), false),
    (`PublicBooleanResultTest.publicBooleanDecision, (fun x y => (PublicBooleanResultTest.publicBooleanDecision x y).toUInt64), false),
    (`PublicBooleanResultTest.publicBooleanWrapped, (fun x y => (PublicBooleanResultTest.publicBooleanWrapped x y).toUInt64), false)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: reusable Boolean helper extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PublicBooleanResultTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 140 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/public Boolean-result IR comparisons passed"
