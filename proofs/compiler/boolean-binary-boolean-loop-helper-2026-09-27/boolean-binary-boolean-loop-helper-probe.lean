import LeanExe.Extract.ScalarFunc
namespace BooleanBinaryBooleanLoopHelperProbe

def direct (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := f i.toUInt64 a.toUInt64 || a
  return a

def bound (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let n := if f count seed then count else count % 7
  let mut a := seed != 0
  for i in [:n.toNat] do
    a := (f i.toUInt64 seed) != a
  return a

def initial (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := f seed count
  for i in [:count.toNat] do
    a := (i.toUInt64 == seed) || !a
  return a

def exit (count seed : UInt64) : Id Bool := do
  let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := !a
    if f i.toUInt64 a.toUInt64 || f seed i.toUInt64 then break
  return a

def unused (count seed : UInt64) : Id Bool := do
  let _f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := (i.toUInt64 == seed) || !a
  return a

def wordTail (count seed : UInt64) : Id UInt64 := do
  let f := fun x y : UInt64 => x + 3 * y == seed
  let mut a := seed != 0
  for i in [:count.toNat] do
    a := (i.toUInt64 == seed) || !a
  return a.toUInt64 + (f a.toUInt64 seed).toUInt64 + (f seed a.toUInt64).toUInt64

end BooleanBinaryBooleanLoopHelperProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanBinaryBooleanLoopHelperProbe.direct, `BooleanBinaryBooleanLoopHelperProbe.bound,
      `BooleanBinaryBooleanLoopHelperProbe.initial, `BooleanBinaryBooleanLoopHelperProbe.exit,
      `BooleanBinaryBooleanLoopHelperProbe.unused, `BooleanBinaryBooleanLoopHelperProbe.wordTail] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
