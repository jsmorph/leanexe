# Boolean do bindings across loop scopes

Step and outer-loop bind extraction now recursively compiles the full action as
Bool.toUInt64 action.expr and stores the resulting encoded Boolean. Exact action
syntax, Bool input/domain checks and standard Bind evidence are retained. The
source rule evaluates the full converted action and the continuation under its
native flag. Step evaluation projects scalar bindings; outer-loop correctness
proves that the same captured flag is preserved under accumulator/index/stop/done
store changes. The scalar extractor terminates independently, so neither loop
extractor needs a new recursion measure.

Reused the checked Boolean-let proofs for source totality, extraction correctness,
acceptance and invariants. Soundness now derives supported actions directly from
successful scalar extraction. The scalar-exclusion proof for loop-containing
source was updated for the reduced bind-premise count. All focused proof modules
pass in the first aggregate build, without axioms or admissions.

The native and syntax tests pass 12,480 native/IR comparisons, 6,912 rejection
checks and 320 admission controls. They cover direct/pure/run/metadata actions,
negation, result annotations, captures, shadowing, unused values, exact
bind types/instances/universes, bounds, initialization and final results.
Explicit Id.run in two native helper-call expressions keeps each bind input Bool.
Prior scalar-bind, loop-let, wrapper and classic-bind fixtures pass 11,992
comparisons, 11,102 invalid-input checks and 790 controls.

The general compiler theorem and eighteen axiom audits pass. Native Lean/V8
agree on 521 inputs across 26 declarations, including seventeen ranges. Eighteen
shared modules retain identical bytes. The full native corpus has 918 declarations.
