import LeanExe.Extract.ScalarFunc

namespace PublicBooleanParametersTest

def publicFlagWord (flag : Bool) (x : UInt64) : UInt64 :=
  if flag then x + 7 else x - 3

def publicWordFlag (x : UInt64) (flag : Bool) : UInt64 :=
  x * 11 + flag.toUInt64

def publicFlagsWord (left right : Bool) : UInt64 :=
  left.toUInt64 * 3 + right.toUInt64 * 7

def publicFlagResult (flag : Bool) (x : UInt64) : Bool := flag && x != 0

def publicWordFlagResult (x : UInt64) (flag : Bool) : Bool := !flag || x == 7

def publicFlagsResult (left right : Bool) : Bool := left != right

def publicFlagLet (flag : Bool) (x : UInt64) : UInt64 :=
  let saved := !flag
  let n := x + flag.toUInt64
  if saved then n / x else n % x

def publicFlagBind (x : UInt64) (flag : Bool) : Id UInt64 := do
  let saved ← pure (!flag)
  let n ← pure (x + saved.toUInt64)
  return if flag then n + 3 else n - 5

def publicFlagCapture (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag && x != 0
  f flag

def publicFlagsDecision (left right : Bool) : Id (Id Bool) :=
  pure (pure (decide (left = right)))

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end PublicBooleanParametersTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`PublicBooleanParametersTest.publicFlagWord, (fun x y => PublicBooleanParametersTest.publicFlagWord (x != 0) y), false),
    (`PublicBooleanParametersTest.publicWordFlag, (fun x y => PublicBooleanParametersTest.publicWordFlag x (y != 0)), false),
    (`PublicBooleanParametersTest.publicFlagsWord, (fun x y => PublicBooleanParametersTest.publicFlagsWord (x != 0) (y != 0)), false),
    (`PublicBooleanParametersTest.publicFlagResult, (fun x y => (PublicBooleanParametersTest.publicFlagResult (x != 0) y).toUInt64), false),
    (`PublicBooleanParametersTest.publicWordFlagResult, (fun x y => (PublicBooleanParametersTest.publicWordFlagResult x (y != 0)).toUInt64), false),
    (`PublicBooleanParametersTest.publicFlagsResult, (fun x y => (PublicBooleanParametersTest.publicFlagsResult (x != 0) (y != 0)).toUInt64), false),
    (`PublicBooleanParametersTest.publicFlagLet, (fun x y => PublicBooleanParametersTest.publicFlagLet (x != 0) y), false),
    (`PublicBooleanParametersTest.publicFlagBind, (fun x y => Id.run (PublicBooleanParametersTest.publicFlagBind x (y != 0))), false),
    (`PublicBooleanParametersTest.publicFlagCapture, (fun x y => (PublicBooleanParametersTest.publicFlagCapture (x != 0) y).toUInt64), false),
    (`PublicBooleanParametersTest.publicFlagsDecision, (fun x y => (PublicBooleanParametersTest.publicFlagsDecision (x != 0) (y != 0)).toUInt64), false)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: public parameter extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else PublicBooleanParametersTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 140 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/public Boolean parameter IR comparisons passed"
