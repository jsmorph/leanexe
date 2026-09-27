# Standard wrappers around Boolean predicate calls

Candidate `ad17571ea394ad63487db480a39887c8145e55c4` admits converted Bool-input calls under standard pure,
Id.run and metadata wrappers. Wrappers can nest and retain standard Id result
annotations and surrounding negation. Calls compose through saved flags, scalar
and loop-step conditions, helper arguments and loop calculations.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 23,988 native/IR comparisons, 16,716 invalid-input checks and 804 controls.
- Prior tests pass 15,572 comparisons, 11,598 invalid-input checks and 828 controls.
- The full native corpus contains 900 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Boolean do binds, direct Boolean helper results, broader annotations and
full-dialect compiler correctness remain subsequent work.
