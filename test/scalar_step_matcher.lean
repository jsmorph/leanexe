import LeanExe.Extract.ScalarStepMatcher

namespace StepMatcherTest

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

end StepMatcherTest
namespace StepMatcherTest

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

end StepMatcherTest

run_elab do
  let env ← Lean.getEnv
  let mut recognized : Nat := 0
  for (name, expected) in [(`StepMatcherTest.direct, 1), (`StepMatcherTest.helper, 1),
      (`StepMatcherTest.nested, 1), (`StepMatcherTest.retained, 1)] do
    let some info := env.find? name | throwError "missing declaration"
    let some value := info.value? | throwError "missing body"
    let matchers := value.getUsedConstants.filter fun called =>
      (LeanExe.Extract.Core.findStepMatcher? env called).isSome
    unless matchers.size == expected do
      throwError "{name}: found {matchers.size} checked matchers, expected {expected}; constants {value.getUsedConstants}"
    recognized := recognized + matchers.size
  unless (LeanExe.Extract.Core.findStepMatcher? env `StepMatcherTest.dispatcher).isSome do
    throwError "canonical dispatcher with an ordinary name rejected"
  let mut rejected : Nat := 0
  for name in [`StepMatcherTest.wrapped, `StepMatcherTest.unsafeDispatcher,
      `StepMatcherTest.fixedUniverse, `StepMatcherTest.direct, `StepMatcherTest.missing, ``ForInStep.casesOn] do
    if (LeanExe.Extract.Core.findStepMatcher? env name).isSome then
      throwError "unsupported matcher declaration {name} admitted"
    rejected := rejected + 1
  unless recognized == 4 && rejected == 6 do throwError "unexpected counts"
  Lean.logInfo m!"{recognized} generated matcher references and one named dispatcher recognized; {rejected} unsupported declarations rejected"

#print axioms LeanExe.Source.Scalar.StepMatcher.denote_cases
#print axioms LeanExe.Extract.Core.findStepMatcher_sound
#print axioms LeanExe.Extract.Core.findStepMatcher_accepts
