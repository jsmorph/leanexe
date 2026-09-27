import LeanExe.Extract.ScalarEnvironmentFunc

namespace StepMatcherExpansionTest

def direct (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => .yield value
    | .yield value => .done value

def helper (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let f := fun result : ForInStep Bool =>
      match result with
      | .done value => if i.toUInt64 == seed then .done (!value) else .yield flag
      | .yield value => .yield (value != flag)
    f (if flag then .done false else .yield true)

def nested (count seed : UInt64) : Bool :=
  forIn (m := Id) [:count.toNat] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value =>
      let inner : ForInStep Bool := .yield (!value)
      match inner with
      | .done value => .done (value != flag)
      | .yield value => .yield value
    | .yield value => .yield (value != flag)

def retained (count seed : UInt64) : Id Bool :=
  forIn (m := Id) [1:count.toNat:3] (seed == 0) fun i flag =>
    let result : ForInStep Bool := if i.toUInt64 == seed then .done (!flag) else .yield flag
    match result with
    | .done value => pure (ForInStep.yield value)
    | .yield value => pure (ForInStep.done value)

end StepMatcherExpansionTest
namespace StepMatcherExpansionTest

def dispatcher (motive : ForInStep Bool → Sort u) (value : ForInStep Bool)
    (doneBody : ∀ flag, motive (.done flag)) (yieldBody : ∀ flag, motive (.yield flag)) : motive value :=
  ForInStep.casesOn (motive := fun value => motive value) value
    (fun flag => doneBody flag) (fun flag => yieldBody flag)

def wrapped (motive : ForInStep Bool → Sort u) (value : ForInStep Bool)
    (doneBody : ∀ flag, motive (.done flag)) (yieldBody : ∀ flag, motive (.yield flag)) : motive value :=
  id (ForInStep.casesOn (motive := fun value => motive value) value
    (fun flag => doneBody flag) (fun flag => yieldBody flag))

unsafe def unsafeDispatcher (motive : ForInStep Bool → Sort u) (value : ForInStep Bool)
    (doneBody : ∀ flag, motive (.done flag)) (yieldBody : ∀ flag, motive (.yield flag)) : motive value :=
  ForInStep.casesOn (motive := fun value => motive value) value
    (fun flag => doneBody flag) (fun flag => yieldBody flag)

def fixedUniverse (motive : ForInStep Bool → Type) (value : ForInStep Bool)
    (doneBody : ∀ flag, motive (.done flag)) (yieldBody : ∀ flag, motive (.yield flag)) : motive value :=
  ForInStep.casesOn (motive := fun value => motive value) value
    (fun flag => doneBody flag) (fun flag => yieldBody flag)

end StepMatcherExpansionTest

run_elab do
  let env ← Lean.getEnv
  let programs : List (Lean.Name × (UInt64 → UInt64 → Bool)) := [
    (`StepMatcherExpansionTest.direct, StepMatcherExpansionTest.direct),
    (`StepMatcherExpansionTest.helper, StepMatcherExpansionTest.helper),
    (`StepMatcherExpansionTest.nested, StepMatcherExpansionTest.nested),
    (`StepMatcherExpansionTest.retained, StepMatcherExpansionTest.retained)]
  let mut comparisons : Nat := 0
  let mut rejected : Nat := 0
  for (name, native) in programs do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    if (LeanExe.Extract.Core.extractScalarFunc name none info.type value).isSome then
      throwError "fixed match probe no longer measures the environment path"
    let some func := LeanExe.Extract.Core.extractScalarEnvironmentFunc env name (some "entry") info.type value |
      throwError "environment extraction rejected {name}"
    let module_ : LeanExe.IR.Module := { funcs := #[func] }
    for count in ([0, 1, 2, 7, 16, 31] : List UInt64) do
      for seed in ([0, 1, 0x8000000000000000, 0xffffffffffffffff] : List UInt64) do
        let expected := (native count seed).toUInt64
        let actual := module_.evalFunc 0 [count, seed]
        unless actual == expected do throwError "{name}({count}, {seed}): {actual} != {expected}"
        comparisons := comparisons + 1
    for replacement in [`StepMatcherExpansionTest.wrapped, `StepMatcherExpansionTest.unsafeDispatcher,
        `StepMatcherExpansionTest.fixedUniverse, `StepMatcherExpansionTest.missing] do
      let changed := value.replace fun expression => match expression with
        | .const called levels => if (LeanExe.Extract.Core.findStepMatcher? env called).isSome then
            some (.const replacement levels) else none
        | _ => none
      if (LeanExe.Extract.Core.extractScalarEnvironmentFunc env name none info.type changed).isSome then
        throwError "unsupported dispatcher {replacement} admitted"
      rejected := rejected + 1
    let wrongLevel := value.replace fun expression => match expression with
      | .const called _ => if (LeanExe.Extract.Core.findStepMatcher? env called).isSome then
          some (.const called [.zero]) else none
      | _ => none
    if (LeanExe.Extract.Core.extractScalarEnvironmentFunc env name none info.type wrongLevel).isSome then
      throwError "unsupported matcher universe admitted"
    rejected := rejected + 1
  unless comparisons == 96 && rejected == 20 do throwError "unexpected test counts"
  Lean.logInfo m!"{comparisons} native/expanded IR comparisons and {rejected} invalid-input tests passed"

#print axioms LeanExe.Extract.Core.expandStepMatchers_normalizes
#print axioms LeanExe.Extract.Core.expandStepMatchers_accepts
#print axioms LeanExe.Extract.Core.extractScalarEnvironmentFunc_correct
