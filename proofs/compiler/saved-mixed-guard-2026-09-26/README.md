# Saved Boolean variables in mixed propositional guards

Candidate `fd0610cd29157787b336b85b65ca748f1edee2c0` admits saved Boolean flags on either side of
propositional conjunctions and disjunctions, including nested mixed trees,
Boolean and propositional negation, ordinary/dependent word and Boolean
choices, saved decisions, helper bodies and loop break/continue. Each flag is
checked as a Boolean conversion. Standard decision evidence preserves its exact
variable; arithmetic leaves retain proved annotation equivalence.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 18,100 native/IR comparisons, 11,008 invalid-input checks and 256 controls.
- Prior tests pass 10,328 comparisons, 7,625 invalid-input checks and 512 controls.
- The full native corpus contains 986 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work; build and test logs retain both the
failed foundation proofs and fixture, and successful checks. Validation uses pinned Lean 4.34.0-rc2,
Node 24.13.0 and the authorized serial local runner.

Direct helper calls and compound Boolean expressions inside mixed propositions,
broader annotations and full-dialect compiler correctness remain subsequent work.
