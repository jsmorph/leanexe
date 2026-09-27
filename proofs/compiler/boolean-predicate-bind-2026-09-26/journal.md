# Scalar Boolean do bindings

The scalar bind extractor now recursively compiles the complete Boolean action
as Bool.toUInt64 action.expr and installs the resulting encoded flag. It retains
exact BooleanAction syntax and standard Bind/type checks. The source rule evaluates
that encoded action followed by the body in a Boolean binding. Source totality
uses the existing conversion-result theorem to recover the native flag.

Reused the Boolean-let proof structure for bind acceptance, correctness and
invariants. The action parser's reconstruction theorem supplies the termination
bound under scalarExtractionSize. Source-to-IR proofs pass on the first aggregate
build, without a measure change or any new axioms/admissions.

The syntax and rejection matrices pass 8,064 native/IR comparisons, 9,216 invalid
inputs and 672 controls. They cover direct/pure/run/metadata actions, nested
wrappers, negation, Id result annotations, exact bind types/instances/universes,
invalid used and unused actions, and value/function kind separation.
Native examples add 180 comparisons covering nested binds, choices, captured
flags and helpers, shadowing, unused actions and scalar calculations in loops.
Two initial native examples applied addition to an Id UInt64 helper result;
explicit Id.run makes the standard arithmetic instance available. No compiler
change was needed. The failed fixture log is retained.

Earlier wrapper, Boolean-bind and saved/dependent-Boolean fixtures pass 6,468
comparisons, 5,608 invalid inputs and 422 controls (including two metadata-action
controls). Loop-step and loop-containing Boolean bind continuations are next;
this increment covers scalar continuations and scalar subexpressions in loops.

The general compiler theorem and eighteen axiom audits pass. Native Lean/V8
agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen
shared modules retain identical bytes. The full native corpus has 910 declarations.
