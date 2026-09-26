# Negated converted Boolean-input predicate calls

The source converted-call rule now retains any number of Boolean Not wrappers.
Its result applies the same GuardNegation.denote operation to the native helper
result before encoding it as a UInt64. Function bindings still select the
Boolean argument interpretation; word-input predicates retain their existing
path. Source totality, extraction acceptance/soundness, evaluation correctness
and structural IR invariants pass for arbitrary negation counts.

The shared booleanWordNegation lowering keeps the original expression at zero
negations. For a positive count it uses the existing proved word-to-Boolean,
negation and Boolean-to-word operations. Separate correctness and structural
preservation lemmas connect those operations to the generalized source rule.
The scalar change applies in all previously admitted helper declaration scopes.

The first equation check needed to unfold BooleanLocal.expr in its parser
acceptance hypothesis before rewriting the raw negated application. After that
syntax adjustment the extractor, source semantics and scalar proof suite pass.
The initial diagnostic is retained. The recursive argument-size proof now uses
the parser's operand bounds at both the call and its Boolean argument.

Ten native examples pass 180 comparisons. Systematic scalar, step and outer-loop
syntax checks pass 3,968 comparisons and 3,072 invalid-input tests, including
zero through three negations, binder kinds, result Id layers, declaration flags,
and literal arguments. Previous unnegated Boolean-input helpers and word-input
predicate syntax pass 1,484 comparisons and 864 invalid-input checks.

The general compiler theorem and all eighteen axiom audits pass. Native Lean/V8
agree on 1,621 inputs across 86 declarations, including 43 ranges. All 76 prior
modules retain identical bytes. The full native corpus contains 804 declarations.
