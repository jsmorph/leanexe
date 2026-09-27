import LeanExe.Extract.ScalarFunc
namespace PredicateBodyWordProbe

def predicateBodyWordRepeated (x y : UInt64) : UInt64 :=
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0)
  (f x).toUInt64 + (f y).toUInt64 + x

def predicateBodyWordBoolean (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => (let g := fun n : UInt64 => n == y || b; g x && g 0)
  if f (x == 0) then x + 7 else y * 3

def predicateBodyWordUnused (x y : UInt64) : UInt64 :=
  let _unused := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0)
  x + y

def predicateBodyWordCapture (x y : UInt64) : UInt64 :=
  let p := fun n : UInt64 => n == y
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g x && g 0)
  if _h : f (x == 0) ≠ f (y == 0) then x + 3 else y + 11

def predicateBodyWordProposition (x y : UInt64) : UInt64 :=
  if x < y ∧ (let f := fun n : UInt64 => (let g := fun k : UInt64 => k == y; g n || g 0); f x && f y) then x + 7 else y + 3

def predicateBodyWordDo (x y : UInt64) : UInt64 :=
  let f := fun b : Bool => Id.run do
    let g := fun k : Bool => k || x == y
    return g b && g (y == 0)
  if _h : f (x == 0) then x + y else x - y

def rangePredicateBodyWordStep (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g a); (f a).toUInt64 + (f i.toUInt64).toUInt64) = 1 then
      a := a + i.toUInt64 + 7
    else a := a * 3 + 1
  return a

def rangePredicateBodyWordExit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if _h : (let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g a && g seed); (f (i.toUInt64 == 0)).toUInt64) = 1 then break
  return a

def rangePredicateBodyWordContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    if (let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0)); f a || f i.toUInt64) ∧ a ≤ seed then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangePredicateBodyWordTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return (let f := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g a && g 0); (f (a == 0)).toUInt64 + (f (a == seed)).toUInt64) + a

end PredicateBodyWordProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`PredicateBodyWordProbe.predicateBodyWordRepeated, `PredicateBodyWordProbe.predicateBodyWordBoolean, `PredicateBodyWordProbe.predicateBodyWordUnused, `PredicateBodyWordProbe.predicateBodyWordCapture, `PredicateBodyWordProbe.predicateBodyWordProposition, `PredicateBodyWordProbe.predicateBodyWordDo, `PredicateBodyWordProbe.rangePredicateBodyWordStep, `PredicateBodyWordProbe.rangePredicateBodyWordExit, `PredicateBodyWordProbe.rangePredicateBodyWordContinue, `PredicateBodyWordProbe.rangePredicateBodyWordTail] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
