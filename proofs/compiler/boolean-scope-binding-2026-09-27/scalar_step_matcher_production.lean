import LeanExe.Extract.Arithmetic

namespace StepMatcherProductionTest

def stepDispatcher (motive : ForInStep Bool → Sort u) (value : ForInStep Bool)
    (doneBody : ∀ flag, motive (.done flag)) (yieldBody : ∀ flag, motive (.yield flag)) : motive value :=
  ForInStep.casesOn (motive := fun value => motive value) value
    (fun flag => doneBody flag) (fun flag => yieldBody flag)

def rangeBooleanStepMatchDirect (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .yield value
    | .yield value => .done value

def rangeBooleanStepMatchHelper (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool =>
      match result with
      | .done value => if i.toUInt64 == seed then .done (!value) else .yield flag
      | .yield value => .yield (value != flag)
    f (if flag then .done false else .yield true)

def rangeBooleanStepMatchNested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value =>
      let inner : ForInStep Bool := .yield (!value)
      match inner with
      | .done value => .done (value != flag)
      | .yield value => .yield value
    | .yield value => .yield (value != flag)

def rangeBooleanStepMatchRetained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => pure (ForInStep.yield value)
    | .yield value => pure (ForInStep.done value)

def rangeBooleanStepMatchIdentity (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .done value
    | .yield value => .yield value

def rangeBooleanStepMatchContinue (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .yield value
    | .yield value => .yield value

def rangeBooleanStepMatchFlagInput (count : UInt64) (seed : Bool) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] seed fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 % (3 : UInt64) == 0 then .done (!flag) else .yield flag
    match result with
    | .done value => .yield (value != seed)
    | .yield value => .yield (!value)

def rangeBooleanStepMatchWordTail (count seed : UInt64) : UInt64 :=
  let flag : Bool := forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .yield value
    | .yield value => .done value
  if flag then seed + count else seed * 3

def rangeBooleanStepMatchDispatcher (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    stepDispatcher (fun _ => ForInStep Bool)
      (if i.toUInt64 == seed then .done (!flag) else .yield flag)
      (fun value => .yield value) (fun value => .done value)


end StepMatcherProductionTest
open StepMatcherProductionTest

run_elab do
  let env ← Lean.getEnv
  let programs : List (Lean.Name × (UInt64 → UInt64 → UInt64)) := [
    (`StepMatcherProductionTest.rangeBooleanStepMatchDirect, fun x y => (rangeBooleanStepMatchDirect x y).toUInt64),
    (`StepMatcherProductionTest.rangeBooleanStepMatchHelper, fun x y => (rangeBooleanStepMatchHelper x y).toUInt64),
    (`StepMatcherProductionTest.rangeBooleanStepMatchNested, fun x y => (rangeBooleanStepMatchNested x y).toUInt64),
    (`StepMatcherProductionTest.rangeBooleanStepMatchRetained, fun x y => (rangeBooleanStepMatchRetained x y).toUInt64),
    (`StepMatcherProductionTest.rangeBooleanStepMatchIdentity, fun x y => (rangeBooleanStepMatchIdentity x y).toUInt64),
    (`StepMatcherProductionTest.rangeBooleanStepMatchContinue, fun x y => (rangeBooleanStepMatchContinue x y).toUInt64),
    (`StepMatcherProductionTest.rangeBooleanStepMatchFlagInput, fun x y => (rangeBooleanStepMatchFlagInput x (y != 0)).toUInt64),
    (`StepMatcherProductionTest.rangeBooleanStepMatchWordTail, fun x y => rangeBooleanStepMatchWordTail x y),
    (`StepMatcherProductionTest.rangeBooleanStepMatchDispatcher, fun x y => (rangeBooleanStepMatchDispatcher x y).toUInt64)]
  let mut comparisons : Nat := 0
  for (name, native) in programs do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    if (LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome then
      throwError "fixed match probe no longer measures the environment path"
    let .ok module_ := LeanExe.Extract.Arithmetic.compileEnvironment env `StepMatcherProductionTest name |
      throwError "strict production compiler rejected {name}"
    let .ok normal := LeanExe.Extract.Core.compileEnvironment env `StepMatcherProductionTest name |
      throwError "ordinary production compiler rejected {name}"
    unless LeanExe.Wasm.Binary.CoreWasm.moduleBytes module_ == LeanExe.Wasm.Binary.CoreWasm.moduleBytes normal do
      throwError "compiler entries emitted different bytes for {name}"
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := native count seed
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do throwError "{name}({count}, {seed}): {actual} != {expected}"
        comparisons := comparisons + 1
  unless comparisons == 216 do throwError "unexpected test counts"
  Lean.logInfo m!"{comparisons} native/production IR comparisons passed across nine declarations"
