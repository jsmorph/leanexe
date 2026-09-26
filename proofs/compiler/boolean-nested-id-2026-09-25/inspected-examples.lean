import LeanExe.Extract.ScalarFunc
namespace BooleanNestedIdInspect

def operators (x y : UInt64) : UInt64 :=
  (Id.run (pure (x == 0)) && Id.run (pure (y != 0))).toUInt64 + x

def binding (x y : UInt64) : UInt64 :=
  (let flag : Id Bool := x == 0; Id.run flag || y != 0).toUInt64 + y

def nested (x y : UInt64) : UInt64 :=
  (!(Id.run (pure (Id.run (pure (x == y)))) &&
    (let saved : Id (Id Bool) := x != 0; Id.run (Id.run saved)))).toUInt64 + x

def helper (x y : UInt64) : UInt64 :=
  let outer := x != 0
  let f := fun flag : Bool =>
    (Id.run (pure flag) && (let saved : Id Bool := outer; Id.run saved)).toUInt64 + x
  f (Id.run (pure (y == 0)))

def range (count seed : UInt64) : UInt64 := Id.run do
  let mut a := seed
  for i in [:count.toNat] do
    let stop := Id.run (pure (let value : Id Bool := (a + UInt64.ofNat i) % 7 == 0
                            Id.run value && Id.run (pure (seed != 0))))
    a := a + UInt64.ofNat i + 1
    if stop then break
  return a
end BooleanNestedIdInspect

set_option pp.all true in
run_elab do
  let env ← Lean.getEnv
  for name in [`BooleanNestedIdInspect.operators, `BooleanNestedIdInspect.binding,
      `BooleanNestedIdInspect.nested, `BooleanNestedIdInspect.helper, `BooleanNestedIdInspect.range] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {value}"
    Lean.logInfo m!"accepted: {(LeanExe.Extract.Core.extractScalarFunc name (some "entry") info.type value).isSome}"
