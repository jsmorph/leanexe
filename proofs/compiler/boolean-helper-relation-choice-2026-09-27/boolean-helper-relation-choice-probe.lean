import LeanExe.Extract.ScalarFunc
namespace BooleanHelperRelationChoiceProbe
def booleanHelperRelationChoiceLeft (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) = (x == 0) then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else y == 0).toUInt64 + x

def booleanHelperRelationChoiceRight (x y : UInt64) : UInt64 :=
  (if (x == y) ≠ (Id.run do
      let f := fun b : Bool => !b || y == 0
      return f (x == y) && f (x == 0)) then
    (let g := fun n : UInt64 => n % 3 == 0; g x || g y) else x == 0).toUInt64 + x

def booleanHelperRelationChoiceFalse (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) = false then
    (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) else x == y).toUInt64 + x

def booleanHelperRelationChoiceDependent (x y : UInt64) : UInt64 :=
  (if _h : (let f := fun n : UInt64 => n == y; f x || f 0) =
      (let h := fun n : UInt64 => n % 3 == 0; h x || h y) then
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))
   else (let h := fun n : UInt64 => n % 5 == 0; h x && h y)).toUInt64 + y

def booleanHelperRelationChoiceTrue (x y : UInt64) : UInt64 :=
  (if _h : (let g := fun b : Bool => b || y == 0; g (x == 0) && g (x == y)) ≠ true then
    (let f := fun n : UInt64 => n == y; f x || f 0) else x == y).toUInt64 + x

def booleanHelperRelationChoiceNested (x y : UInt64) : UInt64 :=
  (Id.run do
    if _h : (let f := fun n : UInt64 => n == y; f x || f 0) ≠ false then
      return if (x == 0) = false then
        (let g := fun b : Bool => b || y != 0; g (x == y) && g (x == 0))
        else false
    else return !(let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + x

def rangeHelperRelationChoiceStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if (let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) = (a == seed) then
        (let g := fun b : Bool => !b || seed == 0; g (a == seed) && g (i.toUInt64 == 0)) else a == seed) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperRelationChoiceExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (if _h : (let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) ≠ false then
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))
      else a % 11 == 0) then break
  return a

def rangeHelperRelationChoiceContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if (a == seed) ≠ (let f := fun n : UInt64 => n % 3 == 0; f a || f i.toUInt64) then
        (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))
      else false) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperRelationChoiceTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (if (let f := fun n : UInt64 => n == seed; f a || f 0) = false then
      (let f := fun n : UInt64 => n % 3 == 0; f a && f seed)
    else !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0))).toUInt64 + a

end BooleanHelperRelationChoiceProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanHelperRelationChoiceProbe.booleanHelperRelationChoiceLeft, `BooleanHelperRelationChoiceProbe.booleanHelperRelationChoiceRight, `BooleanHelperRelationChoiceProbe.booleanHelperRelationChoiceFalse, `BooleanHelperRelationChoiceProbe.booleanHelperRelationChoiceDependent, `BooleanHelperRelationChoiceProbe.booleanHelperRelationChoiceTrue, `BooleanHelperRelationChoiceProbe.booleanHelperRelationChoiceNested, `BooleanHelperRelationChoiceProbe.rangeHelperRelationChoiceStep, `BooleanHelperRelationChoiceProbe.rangeHelperRelationChoiceExit, `BooleanHelperRelationChoiceProbe.rangeHelperRelationChoiceContinue, `BooleanHelperRelationChoiceProbe.rangeHelperRelationChoiceTail] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
