import LeanExe.Extract.ScalarFunc
namespace BooleanStepBindProbe

def word (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let n ← pure (i.toUInt64 + seed)
    flag := flag != (n % 3 == 0)
  return flag

def boolean (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let b ← pure (i.toUInt64 == seed)
    flag := flag != b
  return flag

def joinedWord (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let n ← if flag then pure (i.toUInt64 + seed) else pure (seed + 1)
    flag := n % 3 == 0
    if flag then break
  return flag

def joinedBoolean (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let b ← if flag then pure (i.toUInt64 == seed) else pure (seed == 0)
    flag := b != flag
  return flag

end BooleanStepBindProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanStepBindProbe.word, `BooleanStepBindProbe.boolean,
      `BooleanStepBindProbe.joinedWord, `BooleanStepBindProbe.joinedBoolean] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
