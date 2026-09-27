import LeanExe.Extract.ScalarFunc
namespace PredicateOuterBooleanBodyProbe

def wordTail (count seed : UInt64) : Bool := Id.run do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f a then break
    a := a + i.toUInt64 + 1
  return f a

def booleanTail (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (a == 0) then break
    a := a + i.toUInt64 + 1
  return f (a == seed)

def booleanAccumulator (count seed : UInt64) : Bool := Id.run do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut flag := seed == 0
  for i in [:count.toNat] do
    flag := f flag || i.toUInt64 == seed
  return flag

def wrappedTail (count seed : UInt64) : Id Bool := do
  let f := fun b : Bool => Id.run do
    let g := fun n : UInt64 => n == seed || b
    return g count && g 0
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if f (a == 0) then break
  return f (a == seed)

def unused (count seed : UInt64) : Bool := Id.run do
  let _unused := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (count == 0) && g (seed == 0))
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if a % 7 == 0 then break
  return a == seed

end PredicateOuterBooleanBodyProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`PredicateOuterBooleanBodyProbe.wordTail, `PredicateOuterBooleanBodyProbe.booleanTail,
      `PredicateOuterBooleanBodyProbe.booleanAccumulator, `PredicateOuterBooleanBodyProbe.wrappedTail,
      `PredicateOuterBooleanBodyProbe.unused] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
