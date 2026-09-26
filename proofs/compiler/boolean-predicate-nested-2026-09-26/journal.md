# Nested Boolean-input predicate calls

The converted-call rule now accepts an argument through its own admitted
Bool.toUInt64 evaluation. An independent syntax-inversion theorem proves that
this evaluation produces an encoded Boolean. This supplies the native Bool
required by source totality without admitting word values as Boolean arguments.
The existing LocalCall.head simplification theorem discharged application-root
exclusions; no additional syntax hierarchy was needed.

The recursive extractor call compiles that conversion before applying the
Boolean-input closure. The parser's operand-size bound proves termination.
Correctness, acceptance, soundness and IR invariants use the argument induction
hypothesis directly. Their focused builds and the dependent scalar-function
proofs passed on the first attempt.

New examples cover distinct and repeated helpers, inner/outer negation,
lexical captures, nested calls inside helper bodies, Id results, break/continue,
loop bounds and final values. Exact-syntax tests cover two to five nested calls,
all four negation counts, retained Id result annotations and binder variants.
The old rejected f(f literal) fixture is now part of positive coverage. Other
rejections still check wrong domains/results, value/function confusion,
unsupported arguments and unused unsupported bodies.

The initial native-test generator renamed a shared name prefix before its
longer names, leaving three invalid declaration references. Those diagnostics
are retained; fixing only the test references resolved the failure.
Focused tests pass 12,084 native/IR comparisons and 8,640 invalid-input checks.
Prior syntax tests pass 12,896 comparisons and 9,360 invalid-input checks.
The general compiler theorem, audits and independent engine gate remain next.

The general compiler theorem and all eighteen axiom audits pass. Native Lean/V8
agree on 1,801 inputs across 96 declarations, including 47 ranges. All 86 prior
modules retain identical bytes. The full native corpus contains 814 declarations.
