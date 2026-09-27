# Boolean bindings inside converted Boolean results

Converted Boolean bindings now recursively check their value and body when a
Bool-input predicate is referenced. The value is stored as a distinct Boolean
binding; the result is converted after evaluating the body under that binding.
Negation, retained Id annotations, ordinary lets, immediate applications and
named immediate applications retain their parsed syntax. The old lowering remains
in use when no Bool-input predicate is present.

Independent source evaluation specifies the native flag and the body's result.
Totality recovers each Boolean through booleanConversion_result. Correctness
binds the evaluated flag and reuses scalar extraction and negation correctness.
Acceptance, soundness and structural invariants follow the same typed binding.
The parser's binding-size theorem and existing extraction measure prove both
recursive calls smaller than the original expression.

The first proof build found one additional use of the generic Boolean equation
in the word-input predicate soundness branch. Its new binding-dispatch exclusion
is now supplied explicitly; the failed log is retained. No axioms or admissions
were added.

Focused proof verification, including both loop invariants, passes. New tests
pass 7,348 native/IR comparisons, 4,096 invalid-input checks and 512 controls.
The syntax matrix covers both binder forms, Id annotations, negation, all three
binding forms, calls in the value or body and unused flags. The first syntax
fixture needed a multiline record literal with consistent indentation; its failed
log is retained. Prior tests pass 10,350 comparisons, 6,675 invalid-input checks
and 688 admission controls.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 956 declarations.
