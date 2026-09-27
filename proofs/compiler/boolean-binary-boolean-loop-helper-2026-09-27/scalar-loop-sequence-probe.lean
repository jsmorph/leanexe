import LeanExe.Extract.ScalarEnvironmentFunc

namespace ScalarLoopSequenceProbe

def direct (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  for i in [:count.toNat] do a := a * 3 + i.toUInt64
  return a

def dependent (count seed : UInt64) : Id UInt64 := do
  let mut a := seed % 7
  for i in [:count.toNat] do a := (a + i.toUInt64) % 7
  let mut b := seed
  for i in [:a.toNat] do b := b + a + i.toUInt64
  return a + b

def exits (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    a := a + i.toUInt64
    if a % 7 == 0 then break
  let mut b := a
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    b := b + i.toUInt64
    if b % 11 == 0 then break
  return a + b

def unused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := seed
  for i in [:count.toNat] do b := b + i.toUInt64 * 3
  return b

def three (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  for i in [:count.toNat] do a := a * 3 + i.toUInt64
  for i in [:count.toNat] do a := a ^^^ i.toUInt64
  return a

def flag (count seed : UInt64) : Id Bool := do
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut b := false
  for i in [:count.toNat] do b := b || i.toUInt64 == a
  return b

end ScalarLoopSequenceProbe

run_elab do
  let env ← Lean.getEnv
  for name in [`ScalarLoopSequenceProbe.direct, `ScalarLoopSequenceProbe.dependent,
      `ScalarLoopSequenceProbe.exits, `ScalarLoopSequenceProbe.unused,
      `ScalarLoopSequenceProbe.three, `ScalarLoopSequenceProbe.flag] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let accepted := (LeanExe.Extract.Core.extractScalarEnvironmentFunc env name (some "entry") info.type value).isSome
    Lean.logInfo m!"{name}: {accepted}"
