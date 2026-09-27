import LeanExe.Extract.ScalarFunc
namespace PredicateStepBodyProbe

def rangePredicateBodyBreakWord (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 7 == 0; g n || g seed)
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyBreakBoolean (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g a && g seed)
    if f (i.toUInt64 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyContinueWord (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0))
    if f a || f i.toUInt64 then continue
    a := a * 3 + i.toUInt64 + 1
    if f a then break
  return a

def rangePredicateBodyContinueBoolean (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => n % 3 == 0 || b; g a && g seed)
    if f (i.toUInt64 == 0) then continue
    a := a * 3 + i.toUInt64 + 1
    if f (a == seed) then break
  return a

def rangePredicateBodyDependent (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (if _h : n < seed then (let g := fun k : UInt64 => k % 3 == 0; g n || g a) else n == a)
    if _h : f a ≠ f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyCapture (count seed : UInt64) : Id UInt64 := do
  let p := fun n : UInt64 => n % 5 == 0
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g a && g seed)
    a := a + i.toUInt64 + 1
    if f (a == seed) then break
  return a

def rangePredicateBodyUnused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := fun b : Bool => (let g := fun n : UInt64 => n % 3 == 0 || b; g a && g seed)
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a

def rangePredicateBodyWrapped (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => Id.run do
      let g := fun k : Bool => k || a == seed
      return g b && g (i.toUInt64 == 0)
    if _h : f (a % 3 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyNested (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun b : Bool => (let h := fun k : UInt64 => k == n || b; h a && h seed); g (n % 3 == 0) || g (i.toUInt64 == 0))
    if f a then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateBodyId (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : Id UInt64 => Id.run do
      let g := fun k : UInt64 => k == seed
      return g (Id.run n) || g a
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

end PredicateStepBodyProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`PredicateStepBodyProbe.rangePredicateBodyBreakWord, `PredicateStepBodyProbe.rangePredicateBodyBreakBoolean, `PredicateStepBodyProbe.rangePredicateBodyContinueWord, `PredicateStepBodyProbe.rangePredicateBodyContinueBoolean, `PredicateStepBodyProbe.rangePredicateBodyDependent, `PredicateStepBodyProbe.rangePredicateBodyCapture, `PredicateStepBodyProbe.rangePredicateBodyUnused, `PredicateStepBodyProbe.rangePredicateBodyWrapped, `PredicateStepBodyProbe.rangePredicateBodyNested, `PredicateStepBodyProbe.rangePredicateBodyId] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
