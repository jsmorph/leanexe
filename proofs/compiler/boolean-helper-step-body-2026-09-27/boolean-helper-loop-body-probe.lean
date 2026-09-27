import LeanExe.Extract.ScalarFunc
namespace PredicateLoopBodyProbe

def stepWord (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g a)
    if f a && f i.toUInt64 then a := a + i.toUInt64 + 7 else a := a * 3 + 1
  return a

def stepBoolean (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g a && g seed)
    if f (i.toUInt64 == 0) then break
    a := a + i.toUInt64 + 1
  return a

def stepUnused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let _unused := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0))
    a := a + i.toUInt64 + 1
  return a

def stepContinue (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (n % 3 == 0) && g (a == 0))
    if f a || f i.toUInt64 then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def outerWord (count seed : UInt64) : Id UInt64 := do
  let f := fun n : UInt64 => (let g := fun k : UInt64 => k % 3 == 0; g n || g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f a then a := a + i.toUInt64 + 7 else a := a * 3 + 1
  return a

def outerBoolean (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => (let g := fun n : UInt64 => n % 7 == 0 || b; g count && g seed)
  let mut a := seed
  for i in [:count.toNat] do
    if f (a == 0) then break
    a := a + i.toUInt64 + 1
  return a

end PredicateLoopBodyProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`PredicateLoopBodyProbe.stepWord, `PredicateLoopBodyProbe.stepBoolean,
      `PredicateLoopBodyProbe.stepUnused, `PredicateLoopBodyProbe.stepContinue,
      `PredicateLoopBodyProbe.outerWord, `PredicateLoopBodyProbe.outerBoolean] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
