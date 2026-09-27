# Saved Boolean variables in mixed propositional guards

Saved Boolean guards retain the exact variable, Boolean negation count and
propositional negation count. Mixed junctions admit a saved leaf on the left,
right or both sides; recursive guard trees retain all earlier forms. Standalone
Boolean conditions keep their existing parser. Each saved leaf contributes a
Bool.toUInt64 expression to the checked scalar operands and lowers to a word
comparison with one. The source meaning and lowering proofs share that operand.

The size proof required an explicit decidable bound for the constant-name sizes.
The first parser build needed the fallback pattern exclusions and unfolding of
the saved expression in the negation step. The first decision proof used the
conjunction rewrite lemma as if it were an implication; rewriting the assumption
fixes it. These failed logs are preserved. Guard lowering, scalar extraction,
loop extraction and both IR invariants pass.

Native tests pass 180 comparisons across six scalar and four range declarations.
The syntax matrix covers flags on either side or both, nested trees, repeated
Boolean and propositional negation, Id annotations, ordinary/dependent word and
Boolean choices, and saved decisions. It passes 17,920 comparisons, 11,008
invalid-input checks and 256 controls. Arithmetic decision leaves may use proved
equivalent annotations; changed Boolean decision operands are rejected. The
initial fixture needed an explicit Nat annotation on its numeric mode list.
Prior guard, decision, proposition and bind tests pass 10,328 comparisons,
7,625 invalid-input checks and 512 controls.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 986 declarations.
