import LeanExe.Extract.ScalarFunc

namespace BooleanPredicateTest

def booleanPredicateTwice (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  (f (x == y)).toUInt64 + (f (x != 0)).toUInt64 * 3

def booleanPredicateCapture (x y : UInt64) : UInt64 :=
  let flag := x != 0
  let f := fun b : Bool => flag && (b || x == y)
  (f false).toUInt64 + (f (x != y)).toUInt64 * 3

def booleanPredicateWordCapture (x y : UInt64) : UInt64 :=
  let wordPredicate := fun n : UInt64 => n == y
  let f := fun b : Bool => b && wordPredicate x
  (f true).toUInt64 + (f (wordPredicate y)).toUInt64

def booleanPredicateNested (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => !b
  let g := fun b : Bool => (f b).toUInt64 == x
  (g (x == y)).toUInt64 + (g false).toUInt64 * 3

def booleanPredicateScalarCapture (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == 0
  let g := fun n : UInt64 => (f (n == y)).toUInt64 + n
  g x + g y

def booleanPredicateShadow (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => b || x == y
  let saved := (f false).toUInt64
  let f := fun b : Bool => b && saved != 0
  (f (x != 0)).toUInt64 + saved

def booleanPredicateDependent (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => if _h : x < y then b else !b
  if (f (x == y)).toUInt64 == 1 then x + 7 else y - 3

def booleanPredicateId (x y : UInt64) : UInt64 :=
  let f : Bool → Id (Id Bool) := fun b => b && x != y
  (f true).toUInt64 + (f false).toUInt64 * 3

def booleanPredicateUnused (x y : UInt64) : UInt64 :=
  let _f := fun b : Bool => b && x / y == 0
  x - y

def booleanPredicateDo (x y : UInt64) : UInt64 := Id.run do
  let f := fun b : Bool => !b
  let a ← pure (f (x == y)).toUInt64
  let b ← pure (f (x / y == 0)).toUInt64
  return a + b

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BooleanPredicateTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanPredicateTest.booleanPredicateTwice, BooleanPredicateTest.booleanPredicateTwice),
    (`BooleanPredicateTest.booleanPredicateCapture, BooleanPredicateTest.booleanPredicateCapture),
    (`BooleanPredicateTest.booleanPredicateWordCapture, BooleanPredicateTest.booleanPredicateWordCapture),
    (`BooleanPredicateTest.booleanPredicateNested, BooleanPredicateTest.booleanPredicateNested),
    (`BooleanPredicateTest.booleanPredicateScalarCapture, BooleanPredicateTest.booleanPredicateScalarCapture),
    (`BooleanPredicateTest.booleanPredicateShadow, BooleanPredicateTest.booleanPredicateShadow),
    (`BooleanPredicateTest.booleanPredicateDependent, BooleanPredicateTest.booleanPredicateDependent),
    (`BooleanPredicateTest.booleanPredicateId, BooleanPredicateTest.booleanPredicateId),
    (`BooleanPredicateTest.booleanPredicateUnused, BooleanPredicateTest.booleanPredicateUnused),
    (`BooleanPredicateTest.booleanPredicateDo, BooleanPredicateTest.booleanPredicateDo)]
  let mut comparisons : Nat := 0
  for (name, native) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let some func := LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value |
      throwError "{name}: Boolean-input predicate extraction failed"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for (x, y) in BooleanPredicateTest.inputs do
      let expected := native x y
      let actual := module_.evalFunc 0 [x, y]
      unless actual == expected do
        throwError "{name}({x}, {y}): native={expected}, IR={actual}"
      comparisons := comparisons + 1
  unless comparisons == 140 do throwError "unexpected comparison count {comparisons}"
  Lean.logInfo m!"{comparisons} native/Boolean-input predicate IR comparisons passed"
