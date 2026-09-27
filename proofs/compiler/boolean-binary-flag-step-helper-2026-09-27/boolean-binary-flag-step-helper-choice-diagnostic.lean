import LeanExe.Extract.ScalarEnvironmentFunc

namespace BinaryFlagStepHelperTest

def rangeBinaryFlagStepHelperDirect (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    a := f i.toUInt64 seed || a
  return a

def rangeBinaryFlagStepHelperExit (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (x + 3 * y) % 7 == seed % 7
    a := !a
    if f i.toUInt64 seed || f seed i.toUInt64 then break
  return a

def rangeBinaryFlagStepHelperContinue (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (pure (x + 3 * y == seed + a.toUInt64) : Id Bool)
    if Id.run (f i.toUInt64 seed) then continue
    a := !a
  return a

def rangeBinaryFlagStepHelperNested (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x == y
    let g := fun x y : UInt64 => f (x + 3 * y) seed || a
    a := g i.toUInt64 seed && g seed i.toUInt64
  return a

def rangeBinaryFlagStepHelperUnused (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let _f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    a := (i.toUInt64 == seed) || !a
  return a

def rangeBinaryFlagStepHelperWordTail (count seed : UInt64) : Id UInt64 := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    let saved := f i.toUInt64 seed
    if f seed i.toUInt64 then a := saved else a := !saved
  return a.toUInt64 * 3 + seed

def rangeBinaryFlagStepHelperCapturedExit (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => (x + 3 * y) % 7 == (seed + a.toUInt64) % 7
    a := !a
    if f seed (i.toUInt64 + a.toUInt64) || f i.toUInt64 seed then break
  return a

def rangeBinaryFlagStepHelperChoice (count seed : UInt64) : Id Bool := do
  let mut a := seed != 0
  for i in [:count.toNat] do
    let f := fun x y : UInt64 => x + 3 * y == seed + a.toUInt64
    let first := if a then seed else i.toUInt64
    if f first (seed + i.toUInt64) then a := !a else a := f seed i.toUInt64
    if f a.toUInt64 first then break
  return a

def inputs : List (UInt64 × UInt64) :=
  [(0, 0), (1, 0), (0xffffffffffffffff, 0), (0, 1), (1, 1),
   (0xffffffffffffffff, 1), (0x8000000000000000, 2), (42, 3),
   (0xffffffffffffffff, 63), (0x8000000000000001, 64), (0xffffffffffffffff, 65),
   (0x0123456789abcdef, 0xffffffffffffffff), (3, 17), (17, 3)]

end BinaryFlagStepHelperTest


set_option pp.all true in
#print BinaryFlagStepHelperTest.rangeBinaryFlagStepHelperChoice
run_elab do
  let env ← Lean.getEnv
  let name := `BinaryFlagStepHelperTest.rangeBinaryFlagStepHelperChoice
  let some info := env.find? name | throwError "missing"
  let some value := info.value? | throwError "missing body"
  Lean.logInfo m!"environment accepted: {(LeanExe.Extract.Core.extractScalarEnvironmentFunc env name none info.type value).isSome}"
