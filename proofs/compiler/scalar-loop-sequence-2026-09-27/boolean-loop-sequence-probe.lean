import LeanExe.Extract.ScalarEnvironmentFunc

namespace BooleanLoopSequenceProbe

def direct (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b

def dependent (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := a == seed
  for i in [:(a % 7).toNat] do b := b != (i.toUInt64 == seed)
  return b

def exits (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64
    if a % 7 == 0 then break
  let mut b := false
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    b := b || i.toUInt64 == a % 11
    if b then break
  return b

def unused (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == seed
  return b

def three (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  for i in [:count.toNat] do a := a * 3 + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b

def retained (count seed : UInt64) : Id (Id Bool) := do
  let first : Id (Id UInt64) := do
    let mut a := seed
    for i in [:count.toNat] do a := a + i.toUInt64
    return a
  let a ← first
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b

end BooleanLoopSequenceProbe

run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanLoopSequenceProbe.direct, `BooleanLoopSequenceProbe.dependent,
      `BooleanLoopSequenceProbe.exits, `BooleanLoopSequenceProbe.unused,
      `BooleanLoopSequenceProbe.three, `BooleanLoopSequenceProbe.retained] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let accepted := (LeanExe.Extract.Core.extractScalarEnvironmentFunc env name (some "entry") info.type value).isSome
    Lean.logInfo m!"{name}: {accepted}"
