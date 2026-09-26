# Directly applied named Boolean helper proof journal

The new source form represents a local helper whose entire binding body applies
that helper to one argument. The helper accepts UInt64 or Bool and returns Bool,
including standard Id input/result annotations. The exact let name, arrow binder,
lambda binder, domains and result annotation remain in the source expression.

The independent recognizer checks equal arrow and lambda domains, checks the
Boolean result annotation, and removes the helper binder from the argument.
The existing ExprProofBinder drop/lift theorems prove reconstruction and preserve
outer indices. An argument that refers to the helper is rejected. Both the
helper body and argument are checked, including unused values and captured
word/Boolean slots. General repeated helper uses remain subsequent work.

BooleanBindingForm now gives a common size bound from the canonical argument
binding to the retained source form. That bound replaces per-form size proofs
inside BooleanLocal and applies to lets, immediate applications and named
applications. The lexical lowering and its scalar/step correctness proof are
shared by all three forms.

A first size proof required unfolding the application record's expr abbreviation
before omega could use its binding-size bound. The dependent Boolean parser
matcher did not simplify by rewriting the recognizer result under its equation
binder. Splitting that match, using recognizer-result uniqueness, and eliminating
the impossible none case produced a checked proof. The recognizer's independent
acceptance and soundness theorems remain explicit and are included in the
compiler axiom audit. Earlier size/decrease and equation diagnostics are retained.

Source/recognizer, Boolean parser, scalar and loop-step correctness checks pass.
Native and constructed-syntax checks pass 2,200 comparisons and 720 invalid-input
checks. Their coverage includes
captures, nesting, annotations, unused arguments, dependent conditions, Id
control and range exits, plus rejected domain/result/call mismatches.
The general compiler theorem and all sixteen axiom audits pass. Native Lean/V8
agree on 1,587 inputs across 95 declarations, including 27 range declarations.
All 84 previous modules retain identical bytes. The preceding application and
let-annotation fixtures pass 1,496 comparisons and 316 invalid-input checks.
