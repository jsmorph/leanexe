# Compound Boolean expressions in mixed propositional guards

The guard leaf now retains an exact Boolean expression and a source-level proof
that it is outside the closed BooleanGuard grammar. It remains independent of
the extraction implementation. The parser derives that proof from the closed
parser's soundness/acceptance theorems; the new disjointness lemma excludes all
word-comparison conditions. The scalar operand is Bool.toUInt64 of the exact
expression, so existing conversion rules check junctions, relations, choices,
lets, binds, wrappers and metadata. Existing guard lowering is unchanged.

The first parser proof needed separate induction alternatives for the failed
closed-parser check and the fallback expression shape. After that correction,
parser, scalar, loop and invariant proofs pass. The old saved/call syntax tests
construct leaves through concrete syntax rather than the removed index fields;
their expected counts and values are unchanged.

Native tests exposed two bare let propositions. Lean places equality-to-true
inside those lets and substitutes the values into decision evidence. That is a
distinct source form, still unsupported. The retained inspection logs record
both original terms and the substituted evidence. Current native fixtures put
Boolean-valued lets inside Id.run; the raw syntax matrix also checks them inside
Boolean truth conversions. Bare proposition lets are the next capability.

New tests pass 32,436 native/IR comparisons, 16,896 invalid-input checks and 768
controls, including unused unsupported values and invalid proof domains. Prior
checks pass 46,528 comparisons, 30,921 invalid-input checks and 1,024 controls.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1006 declarations.
