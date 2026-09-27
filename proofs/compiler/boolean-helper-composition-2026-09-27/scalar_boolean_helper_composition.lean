import LeanExe.Extract.ScalarFunc

namespace BooleanHelperCompositionTest

def publicBoolHelpersNested (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag
  let g := fun n : UInt64 => f (n != x)
  g (x + 1)

def publicBoolHelpersRepeated (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag && x != 0
  f (x != 7) || f (x == 7)

def publicBoolHelpersWrapped (flag : Bool) (x : UInt64) : Id (Id Bool) :=
  let f := fun b : Bool => b && flag
  pure (pure (f (x != 0) || f (x == 7)))

def publicBoolHelpersInputId (x : UInt64) (flag : Bool) : Bool :=
  let f := fun b : Id (Id Bool) => Id.run b && flag
  let g := fun n : Id UInt64 => f (Id.run n != x)
  g (x + 1) != g x

def publicBoolHelpersWord (flag : Bool) (x : UInt64) : Bool :=
  let f := fun n : UInt64 => n * 13 + x
  let g := fun b : Bool => if b then f (x + 1) else f (x - 1)
  g flag == f x || g (!flag) != 0

def publicBoolHelpersMany (x y : UInt64) : Bool :=
  let f := fun a b c : UInt64 => a + b * 7 - c + x
  f x y 3 == f y x 5 || f 0 1 2 != y

def publicBoolHelpersUnit (flag : Bool) (x : UInt64) : Bool :=
  let f := fun (_ : Unit) (n : UInt64) => n + x + flag.toUInt64
  f () 3 != x && f () x != 0

def publicBoolHelpersShadow (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b != flag
  let f := fun b : Bool => f b && x != 7
  let f := fun n : UInt64 => f (n == x)
  f x || f (x + 7)

def publicBoolHelpersSaved (flag : Bool) (x : UInt64) : Id Bool := do
  let f := fun b : Bool => b && flag
  let g := fun n : UInt64 => f (n != x)
  let saved ← pure (g (x + 1))
  return if saved then g x else !f saved

def publicBoolHelpersUnused (flag : Bool) (x : UInt64) : Bool :=
  let _ignored := fun n : UInt64 => n / (x - x)
  let f := fun b : Bool => b && flag
  let g := fun n : UInt64 => f (n != x)
  g x || g (x + 1)

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanHelperCompositionTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64) × Bool) := [
    (`BooleanHelperCompositionTest.publicBoolHelpersNested, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersNested (x != 0) y).toUInt64), false),
    (`BooleanHelperCompositionTest.publicBoolHelpersRepeated, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersRepeated (x != 0) y).toUInt64), false),
    (`BooleanHelperCompositionTest.publicBoolHelpersWrapped, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersWrapped (x != 0) y).toUInt64), false),
    (`BooleanHelperCompositionTest.publicBoolHelpersInputId, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersInputId x (y != 0)).toUInt64), false),
    (`BooleanHelperCompositionTest.publicBoolHelpersWord, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersWord (x != 0) y).toUInt64), false),
    (`BooleanHelperCompositionTest.publicBoolHelpersMany, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersMany x y).toUInt64), false),
    (`BooleanHelperCompositionTest.publicBoolHelpersUnit, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersUnit (x != 0) y).toUInt64), false),
    (`BooleanHelperCompositionTest.publicBoolHelpersShadow, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersShadow (x != 0) y).toUInt64), false),
    (`BooleanHelperCompositionTest.publicBoolHelpersSaved, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersSaved (x != 0) y).toUInt64), false),
    (`BooleanHelperCompositionTest.publicBoolHelpersUnused, (fun (x y : UInt64) => (BooleanHelperCompositionTest.publicBoolHelpersUnused (x != 0) y).toUInt64), false)]
  let mut comparisons : Nat := 0
  for (name, native, isRange) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean helper composition extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    let inputs := if isRange then
      ([0, 1, 2, 7, 16, 31] : List UInt64).flatMap fun n =>
        ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64).map fun seed => (n, seed)
      else BooleanHelperCompositionTest.inputs
    for (x, y) in inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 140 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean helper composition IR comparisons passed"
