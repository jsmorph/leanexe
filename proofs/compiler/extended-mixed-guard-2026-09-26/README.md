# Compound Boolean leaves in mixed propositional guards

Candidate `c8a0b116c2603919ff0f98d2c7976070f87376a5` admits Boolean junctions, relations, choices, lets,
standard Id binds, wrappers and metadata as leaves of mixed propositions. Each
exact Boolean expression is checked through the existing conversion extractor;
closed Boolean comparisons retain their earlier lowering. Boolean-valued lets
inside Id.run use this grammar. Bare proposition lets with substituted decision
operands remain unsupported and are recorded as the next capability.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 32,436 native/IR comparisons, 16,896 invalid-input checks and 768 controls.
- Prior tests pass 46,528 comparisons, 30,921 invalid-input checks and 1,024 controls.
- The full native corpus contains 1006 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and build/test logs record proof work, the parser proof
correction and inspection of the unsupported proposition-let form. Validation uses pinned Lean 4.34.0-rc2,
Node 24.13.0 and the authorized serial local runner.

Bare proposition lets, standalone negation of local Boolean propositions, broader
annotations and full-dialect compiler correctness remain subsequent work.
