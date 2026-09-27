import LeanExe.Extract.ScalarFunc
namespace BooleanBinaryStepHelperProbe

def direct (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == a
    if f i.toUInt64 seed then a := a + 7 else a := a + 1
  return a

def exit (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == 7
    a := a + i.toUInt64 + 1
    if f a seed || f seed a then break
  return a

def skip (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (pure (x + 3 * y == a) : Id Bool)
    if Id.run (f i.toUInt64 seed) then continue
    a := a * 3 + i.toUInt64 + 1
  return a

def nested (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x == y
    let g := fun x y : UInt64 => f (x + 3 * y) a || f seed y
    a := a + (g i.toUInt64 seed).toUInt64 + (g seed i.toUInt64).toUInt64
  return a

def unused (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => x + 3 * y == a
    a := a + i.toUInt64 + 1
  return a

def wordTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == a
    let saved := (f i.toUInt64 seed).toUInt64
    if f seed a then a := saved + 5 else a := a + saved + 1
  return a * 3 + seed

end BooleanBinaryStepHelperProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanBinaryStepHelperProbe.direct, `BooleanBinaryStepHelperProbe.exit,
      `BooleanBinaryStepHelperProbe.skip, `BooleanBinaryStepHelperProbe.nested,
      `BooleanBinaryStepHelperProbe.unused, `BooleanBinaryStepHelperProbe.wordTail] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
