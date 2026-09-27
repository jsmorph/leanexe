import LeanExe.Extract.ScalarFunc
namespace PredicateOuterFlagTest
def rangePredicateOuterFlagWord (count seed : UInt64) : Bool := Id.run do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f a then break
    a := a + i.toUInt64 + 1
  return f a

def rangePredicateOuterFlagBoolean (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (a == 0) then break
    a := a + i.toUInt64 + 1
  return f (a == seed)

def rangePredicateOuterFlagAccumulator (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut flag := seed == 0
  for i in [:count.toNat] do
    flag := f flag || i.toUInt64 == seed
  return flag

def rangePredicateOuterFlagWrapped (count seed : UInt64) : Id Bool := do
  let f := fun b : Bool => Id.run do
    let g := fun n : UInt64 => n == seed || b
    return g count && g 0
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if f (a == 0) then break
  return f (a == seed)

def rangePredicateOuterFlagUnused (count seed : UInt64) : Bool := Id.run do
  let _unused := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (count == 0) && g (seed == 0))
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a == seed

def rangePredicateOuterFlagCapture (count seed : UInt64) : Bool := Id.run do
  let p := fun n : UInt64 => n % 5 == 0
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (i.toUInt64 == 0) then continue
    a := a + i.toUInt64 + 1
    if f (a == seed) then break
  return f (a == seed)

def rangePredicateOuterFlagBound (count seed : UInt64) : Bool := Id.run do
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (count == 0))
  let mut a := seed
  for i in [:(count + (f seed).toUInt64).toNat] do
    if f a then continue
    a := a * 3 + i.toUInt64 + 1
  return f a

def rangePredicateOuterFlagInitial (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut flag := f (seed == 0)
  for i in [:count.toNat] do
    if f flag then break
    flag := i.toUInt64 == seed
  return f flag

def rangePredicateOuterFlagNested (count seed : UInt64) : Bool := Id.run do
  let f := fun n : UInt64 => (let g := fun b : Bool => (let h := fun k : UInt64 => k == n || b; h count && h seed); g (n % 3 == 0) || g (seed == 0))
  let mut a := seed
  for i in [:count.toNat] do
    if f a then break
    a := a + i.toUInt64 + 1
  return f a

def rangePredicateOuterFlagId (count seed : UInt64) : Id Bool := do
  let f := fun n : Id UInt64 => Id.run do
    let g := fun k : UInt64 => k == seed
    return g (Id.run n) || g count
  let mut a := seed
  for i in [:count.toNat] do
    if f a && f i.toUInt64 then break
    a := a + i.toUInt64 + 1
  return f a

end PredicateOuterFlagTest
run_elab do
  let env ← Lean.getEnv
  for name in [`PredicateOuterFlagTest.rangePredicateOuterFlagWord, `PredicateOuterFlagTest.rangePredicateOuterFlagBoolean, `PredicateOuterFlagTest.rangePredicateOuterFlagAccumulator, `PredicateOuterFlagTest.rangePredicateOuterFlagWrapped, `PredicateOuterFlagTest.rangePredicateOuterFlagUnused, `PredicateOuterFlagTest.rangePredicateOuterFlagCapture, `PredicateOuterFlagTest.rangePredicateOuterFlagBound, `PredicateOuterFlagTest.rangePredicateOuterFlagInitial, `PredicateOuterFlagTest.rangePredicateOuterFlagNested, `PredicateOuterFlagTest.rangePredicateOuterFlagId] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
