# General predicate bodies in dedicated loop-step bindings

Ten fixed native step declarations fail before this change, covering both helper
input kinds, break/continue, dependent choices, captured values and functions,
unused helpers, nested wrappers and Id input normalization. The earlier scalar
loop probes remain distinct positive controls.

Step.Eval and Step.Supported now retain raw predicate bodies. Their premises
still require the scalar Boolean conversion, whose theorem supplies the encoded
Boolean result, totality and IR invariants. The step parser keeps exact domain
and result annotations and validates a body at zero even when unused. It removes
only the redundant BooleanLocal parse. Step result values and done flags retain
the existing source meaning.

The step parser expresses these body parses as Option binds, so functional case
indices remain unchanged. Cases 24 and 45 lose the BooleanLocal value/parse and
pass their raw body directly to the source support constructor. Their recursive
continuation hypotheses no longer take the parsed BooleanLocal argument. The
acceptance and equation proofs retain the same scalar conversion arguments.
Outer-loop helper declarations are unchanged in this capability.

The source, parser and equation target passes (149 build targets). A diagnostic
attempt to inspect the induction theorem through getConstInfo after importing
only ScalarStepEquations failed because the generated theorem was not in that
environment. That diagnostic is retained. The support/correctness target is
built first, then the diagnostic imports ScalarStepSupported where the induction
rule is used. No compiler change is made for the diagnostic failure.

The support, correctness and invariant target passes on its first run (152 targets).

The corrected induction diagnostic passes, confirming cases 24 and 45 use raw
bodies. The public compiler target passes on its first run (196 targets).

All ten fixed step probes now pass unchanged. Native tests pass 240 comparisons;
raw step tests pass 32,256 value/exit comparisons, 19,584 invalid-input checks and
1,152 controls. Both tests pass on their first run. The earlier six loop probes
now have four admitted step forms and two rejected outer-loop forms. The broader
word-result outer-prefix probe is recorded before proceeding to that capability.

Prior tests pass 101,136 comparisons, 94,240 invalid-input checks and 1,104 controls.

The general compiler proof and nineteen axiom audits pass (3377 build targets). Passed 1053 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1527 declarations. Prior tests pass 101136 comparisons, 94240 invalid-input checks and 1104 controls.
