import LeanExe.Extract.ScalarFunc
namespace PredicateRemainingOuterBodyProbe

def wordFromBoolean (count seed : UInt64) : UInt64 :=
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (count == 0) && g (n % 3 == 0))
  let flag := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f a then break
      a := a + i.toUInt64 + 1
    return f a
  if flag then seed + count else seed * 3

def booleanFromBoolean (count seed : UInt64) : UInt64 :=
  let f := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g count && g 0)
  let flag := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f (a == 0) then break
      a := a + i.toUInt64 + 1
    return f (a == seed)
  if flag then seed + count else seed * 3

def wordConditional (count seed : UInt64) : UInt64 :=
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (count == 0) && g (n % 3 == 0))
  if f seed then
    let flag := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if f a then break
        a := a + i.toUInt64 + 1
      return f a
    if flag then seed + count else seed * 3
  else count + seed

def booleanConditional (count seed : UInt64) : UInt64 :=
  let f := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g count && g 0)
  if f (seed == 0) then
    let flag := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if f (a == 0) then break
        a := a + i.toUInt64 + 1
      return f (a == seed)
    if flag then seed + count else seed * 3
  else count + seed

end PredicateRemainingOuterBodyProbe
run_elab do
  let env ← Lean.getEnv
  for name in [`PredicateRemainingOuterBodyProbe.wordFromBoolean,
      `PredicateRemainingOuterBodyProbe.booleanFromBoolean,
      `PredicateRemainingOuterBodyProbe.wordConditional,
      `PredicateRemainingOuterBodyProbe.booleanConditional] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
