# Standalone negation of local Boolean propositions

Saved Boolean truth leaves now represent only the exact equality-to-true form.
Guard.localNegation records one or more propositional Not wrappers around such
a leaf. This gives the parser one representation for a negated local leaf both
at a condition root and under junctions. Direct Boolean truth still uses the
separate Boolean-expression parser. Previous mixed-guard syntax fixtures retain
their input expressions and expected results through test-only constructors
that build the new canonical guard shape.

Source guard sizes, condition membership, decision syntax, proposition exclusion,
parser round-trip and soundness proofs pass. Removing recursion from the leaf
parser also removed its generated induction theorem; a direct split proves its
soundness. A shared guardOperands_negate lemma handles parser reconstruction
through the new saved-leaf fallback. Guard lowering reuses the same word test
and negation operations, with source and IR proofs passing through scalar
extraction. Loop proofs and focused tests are in progress.

Scalar function, loop-step and loop-exit invariant checks pass. Ten new native
examples pass 180 comparisons. The new syntax matrix passes 33,600 comparisons,
23,040 rejections and 480 controls, covering Boolean and propositional negation
counts, wrappers, bindings, calls, compound expressions, ordinary/dependent word
and Boolean results, and saved decisions. All 23 prior test files pass 200,284
comparisons, 114,689 rejections and 4,704 controls. The three mixed-guard matrices
preserve their existing expected values and counts. The engine group includes
two older saved/call negation examples for explicit emitted-byte comparison.
Full theorem, axiom and independent engine checks follow the candidate commit.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 537 inputs across 30 declarations, including thirteen ranges. Twenty shared modules retain identical bytes, including the saved/call negation examples from their original archives. The full native corpus has 1036 declarations.
