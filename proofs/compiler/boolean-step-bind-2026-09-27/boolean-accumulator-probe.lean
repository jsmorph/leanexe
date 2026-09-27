import LeanExe.Extract.ScalarFunc
namespace BooleanAccumulatorProbe

def toggle (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for _ in [:count.toNat] do
    flag := !flag
  return flag

def compareIndex (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed % 3 == 0
  for i in [:count.toNat] do
    flag := flag != (i.toUInt64 % 3 == seed % 3)
  return flag

def conditional (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    if i.toUInt64 % 2 == 0 then flag := !flag
    else flag := flag || i.toUInt64 == seed
  return flag

def earlyExit (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    flag := flag != (i.toUInt64 == seed)
    if flag then break
  return flag

def skipped (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    if i.toUInt64 % 2 == 0 then continue
    flag := !flag
  return flag

def stride (count seed : UInt64) : Id Bool := do
  let mut flag := seed == 0
  for i in [1:count.toNat:3] do
    flag := flag != (i.toUInt64 % 5 == 0)
  return flag

end BooleanAccumulatorProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanAccumulatorProbe.toggle, `BooleanAccumulatorProbe.compareIndex,
      `BooleanAccumulatorProbe.conditional, `BooleanAccumulatorProbe.earlyExit,
      `BooleanAccumulatorProbe.skipped, `BooleanAccumulatorProbe.stride] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"

set_option pp.explicit true in
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanAccumulatorProbe.toggle, `BooleanAccumulatorProbe.earlyExit] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {value}"
