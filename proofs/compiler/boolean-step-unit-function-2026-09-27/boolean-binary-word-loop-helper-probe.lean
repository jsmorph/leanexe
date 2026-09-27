import LeanExe.Extract.ScalarFunc
namespace BooleanBinaryWordLoopHelperProbe

def direct (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + (f i.toUInt64 a).toUInt64 + 1
  return a

def bound (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let n := if f count seed then count else count % 7
  let mut a := seed
  for i in [:n.toNat] do
    a := a + i.toUInt64 + (f a seed).toUInt64
  return a

def initial (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := if f seed 0 then seed + 1 else seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a

def exit (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
    if f a seed || f seed a then break
  return a

def unused (count seed : UInt64) : Id UInt64 := do
  let _f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a

def tail (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64 + 1
  return a + (f a seed).toUInt64 + (f seed a).toUInt64

end BooleanBinaryWordLoopHelperProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanBinaryWordLoopHelperProbe.direct, `BooleanBinaryWordLoopHelperProbe.bound,
      `BooleanBinaryWordLoopHelperProbe.initial, `BooleanBinaryWordLoopHelperProbe.exit,
      `BooleanBinaryWordLoopHelperProbe.unused, `BooleanBinaryWordLoopHelperProbe.tail] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
