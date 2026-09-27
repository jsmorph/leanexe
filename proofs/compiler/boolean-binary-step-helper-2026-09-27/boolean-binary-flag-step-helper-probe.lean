import LeanExe.Extract.ScalarFunc
namespace BooleanBinaryFlagStepHelperProbe

def direct (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    a := f i.toUInt64 seed || a
  return a

def exit (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
    a := !a
    if f i.toUInt64 seed || f seed i.toUInt64 then break
  return a

def skip (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (pure (x + 3 * y == seed + a.toUInt64) : Id Bool)
    if Id.run (f i.toUInt64 seed) then continue
    a := !a
  return a

def nested (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x == y
    let g := fun x y : UInt64 => f (x + 3 * y) seed || a
    a := g i.toUInt64 seed && g seed i.toUInt64
  return a

def unused (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    a := (i.toUInt64 == seed) || !a
  return a

def wordTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    let saved := f i.toUInt64 seed
    if f seed i.toUInt64 then a := saved else a := !saved
  return a.toUInt64 * 3 + seed

end BooleanBinaryFlagStepHelperProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanBinaryFlagStepHelperProbe.direct, `BooleanBinaryFlagStepHelperProbe.exit,
      `BooleanBinaryFlagStepHelperProbe.skip, `BooleanBinaryFlagStepHelperProbe.nested,
      `BooleanBinaryFlagStepHelperProbe.unused, `BooleanBinaryFlagStepHelperProbe.wordTail] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
