import Lean
open Lean
#check @ForInStep.casesOn
#check @ForInStep.rec
#print ForInStep.casesOn

def inspectStep (result : ForInStep Bool) : ForInStep Bool :=
  match result with
  | .done value => .yield value
  | .yield value => .done value

set_option pp.all true in
#print inspectStep
run_elab do
  let env ← getEnv
  let some info := env.find? `inspectStep | throwError "missing declaration"
  let some value := info.value? | throwError "missing body"
  logInfo m!"{repr value}"
set_option pp.all true in
#print inspectStep.match_1
run_elab do
  let env ← getEnv
  let some info := env.find? `inspectStep.match_1 | throwError "missing matcher"
  let some value := info.value? | throwError "missing matcher body"
  logInfo m!"matcher parameters: {info.levelParams}"
  logInfo m!"matcher type: {repr info.type}"
  logInfo m!"matcher body: {repr value}"
