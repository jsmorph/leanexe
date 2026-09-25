import LeanExe.Extract.ScalarFunc
namespace IdLetInspect

def word (x y : UInt64) : UInt64 :=
  let value : Id UInt64 := x + y
  Id.run value + y

def boolean (x y : UInt64) : UInt64 :=
  let flag : Id Bool := x == 0
  if Id.run flag && y != 0 then x + y else x - y

def literal (x y : UInt64) : UInt64 :=
  let value : Id (Id UInt64) := 3
  Id.run (Id.run value) + x + y

def helper (x y : UInt64) : UInt64 :=
  let f : Id (UInt64 → UInt64) := fun z => z + x
  f y

def range (count seed : UInt64) : UInt64 := Id.run do
  let outer : Id Bool := seed != 0
  let mut a := seed
  for i in [:count.toNat] do
    let value : Id UInt64 := a + UInt64.ofNat i
    a := Id.run value + 1
    let stop : Id (Id Bool) := a % 7 == 0
    if Id.run (Id.run stop) && Id.run outer then break
  let value : Id UInt64 := a + seed
  return Id.run value
end IdLetInspect

set_option pp.all true in
run_elab do
  let env ← Lean.getEnv
  for name in [`IdLetInspect.word, `IdLetInspect.boolean, `IdLetInspect.literal,
      `IdLetInspect.helper, `IdLetInspect.range] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {value}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isSome}"
