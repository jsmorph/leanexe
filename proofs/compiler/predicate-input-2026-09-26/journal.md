# Retained input annotations on reusable predicates

An independent source rule permits matching standard Id layers on a predicate's
arrow and lambda input types. Its premise evaluates or supports the declaration
with one paired layer removed. The original names, binder annotations, helper
body, continuation and captures remain unchanged. Source totality follows by
induction. The scalar and outer-loop extractors check both domains, the UInt64
input base and the Boolean result before removing that layer and recursing on a
strictly smaller source expression.

The step extractor already has a general function-type dispatch for step-valued
continuations. Its rejected-result branch now checks predicateInputTypes? and
removes a checked input layer. The recognizer has independent acceptance and
soundness theorems, both added to the axiom audit. Existing step-result function
dispatch remains first. An initially drafted separate pattern would have been
hidden by that existing general pattern; it was replaced before checking step
support, and the final design extends the existing dispatch.

Scalar, step and outer-range source totality, extraction equations, acceptance,
soundness, evaluation correctness and IR invariants pass. Source inversion lemmas
needed to unfold the new declaration expression to exclude it from literal and
arithmetic-head cases. Function-induction cases eliminate equal-domain variables;
printing just the relevant hypotheses made that change explicit. The dependent
step matcher required a checked step-type exclusion followed by splitting the
annotation match and applying recognizer uniqueness. Earlier source, recognizer,
equation and induction diagnostics are retained.

Concrete and systematic annotation tests precede the general compiler theorem
and selected native/V8 checks. Test coverage includes scalar, step and outer-loop
scopes, nested input/result Id layers, captures, repeated calls, shadowing, unused
helpers and exact domain/type rejection.

Ten native examples pass 180 native/IR comparisons. Exact-syntax tests across
scalar, step and outer-loop scopes pass 8,928 comparisons and 7,344 invalid-input
checks. Real Lean helper bodies use an explicit UInt64 expectation for operands:
typeclass search does not automatically unfold Id parameters when choosing BEq
or arithmetic instances. This expectation leaves the parameter annotation intact.
The first fixture's elaboration errors are retained. All final examples and
syntax tests pass. The candidate is ready for the general theorem, eighteen axiom
audits and the 51-declaration native/V8 suite.

The general source-to-WASM theorem and all eighteen axiom audits pass. Native Lean/V8 agree on 951 inputs across 51 declarations, including 25 ranges. All 41 previous modules retain identical bytes. The full native corpus contains 769 declarations. Prior outer-predicate and step-result tests pass 2,112 comparisons and 864 invalid-input checks.
