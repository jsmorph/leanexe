# Monadic scalar bindings in Boolean loop steps

The four fixed native probes all reject before editing. The source extension
retains standard Id bind syntax, exact input/domain equality and Boolean step
output annotations, with arbitrary supported Id layers. Word and Boolean bind
rules reuse scalar value semantics and preserve both compiled step projections.
Source totality, type-parser soundness/acceptance, extraction correctness,
acceptance/support and invariants pass on their first focused run (145 targets).

Public integration passes (203 targets). Two direct-bind original probes now
compile. Both conditional-action probes remain rejected because Lean elaborates
the join into a local step-returning continuation. Their original source and
a fully explicit elaboration are preserved for the next capability. Eight of
ten new probe declarations compile; the two conditional-action variants remain
in the fixed diagnostic file rather than the positive native corpus. Syntax
checks pass 13,824 comparisons and 7,488 invalid-input tests on the first run.

The general source-to-WASM theorem and nineteen audits pass (3384 targets). Passed 1005 native Lean / independent Wasm engine comparisons across 52 declarations.
44 prior modules retain identical bytes; 0 changed. Prior tests pass 30480 comparisons and 20736 invalid-input checks. Six fixed accumulator probes remain accepted.
