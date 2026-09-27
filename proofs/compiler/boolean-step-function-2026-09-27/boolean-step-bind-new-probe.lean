import LeanExe.Extract.ScalarFunc

namespace BooleanStepBindTest

def rangeBooleanStepBindWord (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let n ← pure (i.toUInt64 + seed)
    flag := flag != (n % 3 == 0)
  return flag

def rangeBooleanStepBindBoolean (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let b ← pure (i.toUInt64 == seed)
    flag := flag != b
  return flag

def rangeBooleanStepBindChoiceWord (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let n ← if flag then pure (i.toUInt64 + seed) else pure (seed + 1)
    flag := n % 3 == 0
    if flag then break
  return flag

def rangeBooleanStepBindChoiceBoolean (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let b ← if flag then pure (i.toUInt64 == seed) else pure (seed == 0)
    flag := b != flag
  return flag

def rangeBooleanStepBindChain (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let n ← pure (i.toUInt64 + seed)
    let b ← pure (n % 3 == 0 || flag)
    let k ← pure (n + b.toUInt64)
    flag := flag != (b && k % 5 == 0)
  return flag

def rangeBooleanStepBindUnusedWord (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let _unused ← pure (i.toUInt64 + seed)
    flag := !flag
  return flag

def rangeBooleanStepBindUnusedBoolean (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [:count.toNat] do
    let _unused ← pure (i.toUInt64 == seed)
    flag := !flag
  return flag

def rangeBooleanStepBindCaptured (count : UInt64) (seed : Bool) : Id Bool := do
  let f := fun n : UInt64 => (let g := fun b : Bool => b || seed; g (n % 3 == 0))
  let mut flag := seed
  for i in [:count.toNat] do
    let b ← pure (f i.toUInt64)
    flag := flag != b
    if flag then break
  return flag

def rangeBooleanStepBindContinue (count seed : UInt64) : Bool := Id.run do
  let mut flag := seed == 0
  for i in [1:count.toNat:3] do
    let b ← pure (i.toUInt64 % 2 == 0)
    if b then continue
    let n ← pure (i.toUInt64 + seed)
    flag := flag != (n % 3 == 0)
  return flag

def rangeBooleanStepBindWordTail (count seed : UInt64) : UInt64 :=
  let flag := Id.run do
    let mut a := seed == 0
    for i in [:count.toNat] do
      let b ← pure (i.toUInt64 == seed)
      a := a != b
      if a then break
    return a
  if flag then seed + count else seed * 3

end BooleanStepBindTest

run_elab do
  let env ← Lean.getEnv
  let cases : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`BooleanStepBindTest.rangeBooleanStepBindWord, (fun (x y : UInt64) => (BooleanStepBindTest.rangeBooleanStepBindWord x y).toUInt64)),
    (`BooleanStepBindTest.rangeBooleanStepBindBoolean, (fun (x y : UInt64) => (BooleanStepBindTest.rangeBooleanStepBindBoolean x y).toUInt64)),
    (`BooleanStepBindTest.rangeBooleanStepBindChoiceWord, (fun (x y : UInt64) => (BooleanStepBindTest.rangeBooleanStepBindChoiceWord x y).toUInt64)),
    (`BooleanStepBindTest.rangeBooleanStepBindChoiceBoolean, (fun (x y : UInt64) => (BooleanStepBindTest.rangeBooleanStepBindChoiceBoolean x y).toUInt64)),
    (`BooleanStepBindTest.rangeBooleanStepBindChain, (fun (x y : UInt64) => (BooleanStepBindTest.rangeBooleanStepBindChain x y).toUInt64)),
    (`BooleanStepBindTest.rangeBooleanStepBindUnusedWord, (fun (x y : UInt64) => (BooleanStepBindTest.rangeBooleanStepBindUnusedWord x y).toUInt64)),
    (`BooleanStepBindTest.rangeBooleanStepBindUnusedBoolean, (fun (x y : UInt64) => (BooleanStepBindTest.rangeBooleanStepBindUnusedBoolean x y).toUInt64)),
    (`BooleanStepBindTest.rangeBooleanStepBindCaptured, (fun (x y : UInt64) => (BooleanStepBindTest.rangeBooleanStepBindCaptured x (y != 0)).toUInt64)),
    (`BooleanStepBindTest.rangeBooleanStepBindContinue, (fun (x y : UInt64) => (BooleanStepBindTest.rangeBooleanStepBindContinue x y).toUInt64)),
    (`BooleanStepBindTest.rangeBooleanStepBindWordTail, (fun (x y : UInt64) => BooleanStepBindTest.rangeBooleanStepBindWordTail x y))]
  for (name, _) in cases do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
