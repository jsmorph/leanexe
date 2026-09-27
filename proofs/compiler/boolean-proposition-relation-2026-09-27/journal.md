# Boolean relations in compound propositions

Two saved gaps were confirmed before editing: a nested-Id decision of
`left = right ∨ ¬ left`, and a word conditional with `left ≠ right ∧ left`.
A new independent Boolean proposition leaf preserves either the existing truth
form or the exact Bool Eq/Ne syntax. Relation operands compile separately through
Bool.toUInt64. The new native-meaning lemma connects equality of those encodings
to the original Boolean Eq/Ne decision. Compound lowering reuses the existing
comparison and junction evaluation/invariant proofs.

The first proposed operand bound for a bare relation was false. The saved probe
and size calculations show why: conversion has a larger constant head than the
bare proposition can cover with the existing guard overhead. Junction and Not
syntax provide a sufficient bound, proved once in the leaf module. This
increment therefore admits relations under junctions and negation while retaining
the existing truth-only direct proposition-let fallback. Compound relations
under lets already use the recursive guard path. No global size allowance was
changed. Standalone Boolean relations retain their existing scalar parser path.

The initial source/parser attempts exposed stale truth-only projections in the
guard disjointness proofs and an unspecified witness in acceptance. Generic leaf
lemmas and explicit lowering witnesses resolved these. The native-meaning proof
needed closed zero/one inequalities discharged by the kernel's ordinary decide.
Failed checks and probe sources are retained.

The public source compiler builds. Ten new elaborated declarations pass 180
native/IR comparisons, exercising Boolean parameters/results, nested Id returns,
helpers, lets, range updates, break, continue and a Boolean loop continuation.
The syntax tests pass 44,800 comparisons, 21,248 invalid-input checks and 672
controls across relation polarity, operand syntax, binding/Id annotations,
connectives, negation and five word/Boolean/dependent result forms. They verify
exact source/evidence, reject wrong types/scopes/universes/proof domains, and
preserve standalone relation admission.

Six adjacent test files pass 92,928 comparisons, 56,532 invalid-input checks and
1,856 controls. The two existing saved/call test helpers now accept the generalized
leaf argument; their generated cases and expectations are unchanged. All ten
new declarations are registered in admission, native, V8 and range configurations.

Main advanced to 823008dc during this increment. It is merged into correct as
55a5b1bd, retaining this compiler task. Full source-to-WASM and V8 checks are run
against the following committed candidate. The merged scalar-result theorem is
also checked as a focused target because it is a new module outside the ordinary
audit's imports.

The complete compiler proof and nineteen axiom audits pass. The merged scalar-result theorem and new Boolean relation meaning lemma also check with standard-only axioms. Native Lean/V8 agree on 549 inputs across 28 declarations, including seventeen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1397 declarations.
