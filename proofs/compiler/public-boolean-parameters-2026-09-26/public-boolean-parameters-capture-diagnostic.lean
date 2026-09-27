import LeanExe.Extract.ScalarFunc
open LeanExe.Extract.Core LeanExe.Source.Scalar

def captureFlag (flag : Bool) (_x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag
  f true

def captureWord (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && x != 0
  f flag

def captureBoth (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag && x != 0
  f true

def captureRepeat (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag && x != 0
  f (x != 7) || f (x == 7)

run_elab do
  let env ← Lean.getEnv
  for name in [`captureFlag, `captureWord, `captureBoth, `captureRepeat] do
    let some info := env.find? name | throwError "missing"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(extractScalarFunc name none info.type value).isSome}\n{value}\n{repr value}"
