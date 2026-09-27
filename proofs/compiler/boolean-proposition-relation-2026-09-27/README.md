# Boolean relations in compound propositions

Candidate `de04b83286ea50322d6644be655cb891a25987fa` admits Boolean equality and inequality within
propositional conjunctions, disjunctions and negations. Exact source and decision
syntax is retained; both operands compile through the checked Boolean conversion.
The meaning lemma connects encoded equality to the original Eq/Ne proposition.
Decisions, ordinary/dependent word or Boolean choices, helpers, lets and loop
steps/exits use the same lowering. Standalone relation admission is unchanged.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- The new native-meaning lemma and merged scalar-result theorem pass their audits.
- Native Lean/V8 agree on 549 inputs across 28 declarations, including seventeen ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 44,980 native/IR comparisons, 21,248 invalid-input checks and 672 controls.
- Prior tests pass 92,928 comparisons, 56,532 invalid-input checks and 1,856 controls.
- The full native corpus contains 1397 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records the structural size proof, retained failed
attempts and validation. Checks use pinned Lean 4.34.0-rc2, Node 24.13.0 and the
authorized serial local runner. Main through `823008dc` is merged into correct.
Bare relations directly inside proposition lets and full-dialect compiler
correctness remain open, as do the other deferred capabilities in the manifest.
