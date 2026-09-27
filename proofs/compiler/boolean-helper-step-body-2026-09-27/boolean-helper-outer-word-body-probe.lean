import LeanExe.Extract.ScalarFunc
namespace PredicateOuterBodyProbe

def rangePredicateOuterBodyWord (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f a then a := a + i.toUInt64 + 7 else a := a * 3 + 1
  return a

def rangePredicateOuterBodyBoolean (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (a == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyUnused (count seed : UInt64) : Id UInt64 := do
  let _unused := fun b : Bool => (let g := fun n : UInt64 => n % 3 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a

def rangePredicateOuterBodyBound (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (count == 0))
  let mut a := seed
  for i in [:(count + (f seed).toUInt64).toNat] do
    if f a then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyInitial (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed + (f (seed == 0)).toUInt64
  for i in [:count.toNat] do
    if f (a == seed) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyTail (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 5 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if f a then break
  return a + (f a).toUInt64 + (f seed).toUInt64

def rangePredicateOuterBodyCapture (count seed : UInt64) : Id UInt64 := do
  let p := fun n : UInt64 => n % 5 == 0
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (i.toUInt64 == 0) then continue
    a := a + i.toUInt64 + 1
    if f (a == seed) then break
  return a

def rangePredicateOuterBodyWrapped (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => Id.run do
    let g := fun k : Bool => k || count == seed
    return g b && g (seed == 0)
  let mut a := seed
  for i in [:count.toNat] do
    if _h : f (a % 3 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyNested (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun b : Bool => (let h := fun k : UInt64 => k == n || b; h count && h seed); g (n % 3 == 0) || g (seed == 0))
  let mut a := seed
  for i in [:count.toNat] do
    if f a then break
    a := a + i.toUInt64 + 1
  return a

def rangePredicateOuterBodyId (count seed : UInt64) : Id UInt64 := do
  let f := fun n : Id UInt64 => Id.run do
    let g := fun k : UInt64 => k == seed
    return g (Id.run n) || g count
  let mut a := seed
  for i in [:count.toNat] do
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return a

end PredicateOuterBodyProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`PredicateOuterBodyProbe.rangePredicateOuterBodyWord, `PredicateOuterBodyProbe.rangePredicateOuterBodyBoolean, `PredicateOuterBodyProbe.rangePredicateOuterBodyUnused, `PredicateOuterBodyProbe.rangePredicateOuterBodyBound, `PredicateOuterBodyProbe.rangePredicateOuterBodyInitial, `PredicateOuterBodyProbe.rangePredicateOuterBodyTail, `PredicateOuterBodyProbe.rangePredicateOuterBodyCapture, `PredicateOuterBodyProbe.rangePredicateOuterBodyWrapped, `PredicateOuterBodyProbe.rangePredicateOuterBodyNested, `PredicateOuterBodyProbe.rangePredicateOuterBodyId] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
