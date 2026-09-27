# General predicate bodies before word-result loops

Ten fixed probes reject nested-body predicates before UInt64-result loops. They
cover both predicate input kinds, unused helpers, loop bounds and initial values,
loop bodies and final results, captured predicates, wrappers and Id annotations.
The original outerWord and outerBoolean probes show the same prefix restriction.

The RangeExit predicate binding rules now retain raw Lean expressions. Their
premises continue to require the checked scalar Boolean conversion. The prefix
parser preserves the function and lambda domains and Boolean result annotations,
validates every body at zero even when unused, and creates the same typed closure.
The original helper scope surrounds the loop, preserving captures across loop
states. The NotScalar proof, source totality, equation and acceptance proofs use
the same recursion. Support and invariant cases 13 and 25 no longer carry a
parsed BooleanLocal body argument. The dedicated BooleanRange continuation
dispatcher and other outer grammars remain unchanged in this capability.

The source, parser, equations, support and acceptance target passes on its
first run (167 targets). The focused correctness and invariant targets are next.

The induction diagnostic and the correctness/invariant target pass (171 targets).

The public compiler target passes on its first run (196 targets).

All ten fixed native outer-prefix probes pass unchanged. Native tests pass 240
comparisons. Word-input syntax tests pass 3,456 comparisons and 1,152 invalid-input
checks; Boolean-input tests pass 6,912 comparisons and 2,736 invalid-input checks.
Both syntax files also check valid unused helpers across zero and nonzero loop
counts. All tests passed on their first runs; final runs add exact count checks.
The original six loop probes all pass: two outer-prefix forms were restored and
four step controls retained their behavior. Five new Boolean-result loop probes
remain rejected, identifying the separate continuation grammar for the next step.

Prior tests pass 41,136 comparisons, 25,056 invalid-input checks and 1,152 controls.

The general compiler proof and nineteen axiom audits pass (3377 build targets). Passed 1053 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1537 declarations. Prior tests pass 41136 comparisons, 25056 invalid-input checks and 1152 controls.
