import LeanExe.Extract.ScalarEnvironmentFunc

namespace BooleanPrefixSequenceProbe

def word (count seed : UInt64) : Id UInt64 := do
  let mut flag := false
  for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
  let mut a := seed
  for i in [:count.toNat] do a := if flag then a + i.toUInt64 else a * 3
  return a

def boolean (count seed : UInt64) : Id Bool := do
  let mut flag := false
  for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
  let mut result := flag
  for i in [:count.toNat] do result := result != (i.toUInt64 % 3 == 0)
  return result

def dependent (count seed : UInt64) : Id UInt64 := do
  let mut flag := seed == 0
  for i in [:count.toNat] do flag := flag != (i.toUInt64 == seed)
  let bound := if flag then count else count % 7
  let mut a := seed + flag.toUInt64
  for i in [:bound.toNat] do a := a + i.toUInt64
  return a

def exits (count seed : UInt64) : Id Bool := do
  let mut flag := false
  for i in [:count.toNat] do
    if i.toUInt64 % 3 == 0 then continue
    flag := flag || i.toUInt64 == seed % 7
    if flag then break
  let mut result := flag
  for i in [:count.toNat] do
    result := result != (i.toUInt64 % 5 == 0)
    if result then break
  return result

def unused (count seed : UInt64) : Id UInt64 := do
  let mut flag := false
  for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
  let mut a := seed
  for i in [:count.toNat] do a := a + i.toUInt64
  return a

def alternating (count seed : UInt64) : Id Bool := do
  let mut flag := false
  for i in [:count.toNat] do flag := flag || i.toUInt64 == seed
  let mut a := seed + flag.toUInt64
  for i in [:count.toNat] do a := a + i.toUInt64
  let mut result := flag
  for i in [:count.toNat] do result := result || i.toUInt64 == a % 7
  return result

end BooleanPrefixSequenceProbe

run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanPrefixSequenceProbe.word, `BooleanPrefixSequenceProbe.boolean,
      `BooleanPrefixSequenceProbe.dependent, `BooleanPrefixSequenceProbe.exits,
      `BooleanPrefixSequenceProbe.unused, `BooleanPrefixSequenceProbe.alternating] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let accepted := (LeanExe.Extract.Core.extractScalarEnvironmentFunc env name (some "entry") info.type value).isSome
    Lean.logInfo m!"{name}: {accepted}"
