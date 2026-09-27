import LeanExe.Extract.ScalarFunc
namespace PredicateRemainingOuterTest
def rangePredicateOuterWordFromBoolean (count seed : UInt64) : UInt64 :=
  let f := fun n : UInt64 => (let g := fun b : Bool => b || n == seed; g (count == 0) && g (n % 3 == 0))
  let flag := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f a then break
      a := a + i.toUInt64 + 1
    return f a
  if flag then seed + count else seed * 3

def rangePredicateOuterBooleanFromBoolean (count seed : UInt64) : UInt64 :=
  let f := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g count && g 0)
  let flag := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      if f (a == 0) then break
      a := a + i.toUInt64 + 1
    return f (a == seed)
  if flag then seed + count else seed * 3

def rangePredicateOuterWordConditional (count seed : UInt64) : UInt64 :=
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

def rangePredicateOuterBooleanConditional (count seed : UInt64) : UInt64 :=
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

def rangePredicateOuterDerivedUnused (count seed : UInt64) : UInt64 :=
  let _unused := fun b : Bool => (let g := fun n : UInt64 => n == seed || b; g count && g 0)
  let flag := Id.run do
    let mut a := seed
    for i in [:count.toNat] do
      a := a + i.toUInt64 + 1
      if a % 7 == 0 then break
    return a == seed
  if flag then seed + count else seed * 3

def rangePredicateOuterDerivedWrapped (count seed : UInt64) : Id UInt64 := do
  let f := fun b : Bool => Id.run do
    let g := fun n : UInt64 => n == seed || b
    return g count && g 0
  let flag ← (do
    let mut a := seed
    for i in [:count.toNat] do
      if f (a == 0) then break
      a := a + i.toUInt64 + 1
    return f (a == seed))
  return if flag then seed + count else seed * 3

def rangePredicateOuterChoiceCapture (count seed : UInt64) : UInt64 :=
  let p := fun n : UInt64 => n % 5 == 0
  let f := fun b : Bool => (let g := fun n : UInt64 => p n || b; g count && g seed)
  if f (seed == 0) then
    let flag := Id.run do
      let mut a := seed
      for i in [:count.toNat] do
        if f (i.toUInt64 == 0) then continue
        a := a + i.toUInt64 + 1
        if f (a == seed) then break
      return f (a == seed)
    if flag then seed + count else seed * 3
  else count + seed

def rangePredicateOuterChoiceNested (count seed : UInt64) : Id UInt64 := do
  let f := fun n : Id UInt64 => Id.run do
    let g := fun b : Bool => (let h := fun k : UInt64 => k == Id.run n || b; h count && h seed)
    return g (Id.run n % 3 == 0) || g (seed == 0)
  if f seed then
    let flag ← (do
      let mut a := seed
      for i in [:count.toNat] do
        if f a then break
        a := a + i.toUInt64 + 1
      return f a)
    return if flag then seed + count else seed * 3
  else return count + seed


end PredicateRemainingOuterTest
run_elab do
  let env ← Lean.getEnv
  for name in [`PredicateRemainingOuterTest.rangePredicateOuterWordFromBoolean, `PredicateRemainingOuterTest.rangePredicateOuterBooleanFromBoolean, `PredicateRemainingOuterTest.rangePredicateOuterWordConditional, `PredicateRemainingOuterTest.rangePredicateOuterBooleanConditional, `PredicateRemainingOuterTest.rangePredicateOuterDerivedUnused, `PredicateRemainingOuterTest.rangePredicateOuterDerivedWrapped, `PredicateRemainingOuterTest.rangePredicateOuterChoiceCapture, `PredicateRemainingOuterTest.rangePredicateOuterChoiceNested] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    Lean.logInfo m!"{name}: {(LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome}"
