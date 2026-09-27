import LeanExe.Extract.ScalarFunc
namespace BooleanHelperChoiceProbe
def booleanHelperChoiceCondition (x y : UInt64) : UInt64 :=
  (if (let f := fun n : UInt64 => n == y; f x || f 0) then x == 0 else y == 0).toUInt64 + x

def booleanHelperChoiceYes (x y : UInt64) : UInt64 :=
  (if x == y then (Id.run do
    let f := fun b : Bool => !b || y == 0
    return f (x == y) && f (x == 0)) else y != 0).toUInt64 + x

def booleanHelperChoiceNo (x y : UInt64) : UInt64 :=
  (if x == 0 then x == y else
    !(let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))).toUInt64 + y

def booleanHelperChoiceDependent (x y : UInt64) : UInt64 :=
  (if _h : (let f := fun n : UInt64 => n == y; f x || f 0) then
    (let g := fun b : Bool => !b || y == 0; g (x == y) && g (x == 0))
   else (let h := fun n : UInt64 => n % 3 == 0; h x || h y)).toUInt64 + y

def booleanHelperChoiceNested (x y : UInt64) : UInt64 :=
  (Id.run do
    if _h : (let f := fun n : UInt64 => n == y; f x || f 0) then
      return if x == 0 then
        (let g := fun b : Bool => b || y != 0; g (x == y) && g (x == 0))
        else false
    else return !(let h := fun n : UInt64 => n % 3 == 0; h x && h y)).toUInt64 + x

def booleanHelperChoiceUnused (x y : UInt64) : UInt64 :=
  (if false then (let _unused := fun b : Bool => b && x != 0; x == y)
   else (let f := fun n : UInt64 => n == x; f y && f 0)).toUInt64 + y

def rangeHelperChoiceStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if (let f := fun n : UInt64 => n % 2 == 0; f a && f i.toUInt64) then a == seed else i.toUInt64 == 0) then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangeHelperChoiceExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (if _h : (let f := fun n : UInt64 => n % 7 == 0; f a || f (i.toUInt64 + 1)) then
        !(Id.run do
          let g := fun b : Bool => b || seed == 0
          return g (a == seed) && g (i.toUInt64 == 0))
      else a % 11 == 0) then break
  return a

def rangeHelperChoiceContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (if a == seed then
        (let f := fun b : Bool => !b || a % 2 == 0; f (i.toUInt64 % 3 == 0) && f (a == seed))
      else false) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangeHelperChoiceTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (if a == 0 then (let f := fun n : UInt64 => n == seed; f a || f 0)
    else !(Id.run do
      let g := fun b : Bool => b || seed == 0
      return g (a == seed) && g (a == 0))).toUInt64 + a

end BooleanHelperChoiceProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanHelperChoiceProbe.booleanHelperChoiceCondition, `BooleanHelperChoiceProbe.booleanHelperChoiceYes, `BooleanHelperChoiceProbe.booleanHelperChoiceNo, `BooleanHelperChoiceProbe.booleanHelperChoiceDependent, `BooleanHelperChoiceProbe.booleanHelperChoiceNested, `BooleanHelperChoiceProbe.booleanHelperChoiceUnused, `BooleanHelperChoiceProbe.rangeHelperChoiceStep, `BooleanHelperChoiceProbe.rangeHelperChoiceExit, `BooleanHelperChoiceProbe.rangeHelperChoiceContinue, `BooleanHelperChoiceProbe.rangeHelperChoiceTail] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
