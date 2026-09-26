# Immediate Boolean application proof journal

`BooleanBindingForm` retains either an original let or an immediate lambda
application. The Boolean syntax tree uses the same lexical interpretation for
both forms. A word argument supplies the innermost word slot; a Boolean argument
supplies the innermost Boolean slot. Captured scalar operands retain the
corresponding canonical let context. Size proofs show that these scoped operands
remain smaller than the original source expression, including Id annotations.

Parser soundness reconstructs the exact application, parameter domain and binder
annotation. Parser acceptance covers both input types. The scalar and loop-step
compiler correctness proofs continue to use the same typed bindings and proved
Boolean zero/one representation. No extra compiler-success assumption is added
to source evaluation.

Native examples retain actual lambda applications after elaboration, as checked
by the test. They cover word and Boolean arguments, nested lambdas, captured
flags and scalar functions, unused arguments, dependent conditions, Id actions,
and range break/continue. Constructed syntax varies binder annotations, nested
Id types and negation. Wrong domains, mismatched lexical kinds, unsupported
bodies and missing variables are rejected.

The first annotated native example relied on automatic BEq resolution for
Id UInt64. Lean did not infer the underlying UInt64 instance, even with a type
ascription. The fixture now supplies the standard UInt64 equality instance
explicitly. No compiler acceptance rule was changed for that elaboration issue.
The diagnostic is retained. Test counters have explicit Nat types, and the
unsupported-expression test names an existing UInt64 function.

The focused checks pass 1,192 native/IR comparisons and 216 invalid-input tests.
The general source-to-WASM theorem and all fourteen axiom audits pass. Native
Lean/V8 agree on 1,403 inputs across 84 declarations, including 24 range
declarations. All 73 previous modules retain identical bytes. Previous binding
and saved-decision fixtures pass 792 comparisons and 168 rejection checks.
Named Boolean helper bindings and calls remain the next capability; full
dialect correctness remains unfinished.
