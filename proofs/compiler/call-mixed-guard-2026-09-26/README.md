# Boolean helper calls in mixed propositional guards

Candidate `5b28c84cb756f71eb30922bfede697675e6bc483` admits direct calls to Bool- and UInt64-input Boolean
helpers as leaves in mixed propositions. Arguments, nested calls, captures,
negation and Id result annotations are checked by the existing typed extractor.
This composes through ordinary/dependent word and Boolean choices, saved
decisions, helper bodies and loop break/continue.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 18,100 native/IR comparisons, 12,288 invalid-input checks and 256 controls.
- Prior tests pass 28,428 comparisons, 18,633 invalid-input checks and 768 controls.
- The full native corpus contains 996 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and build/test logs record the successful proof work. Validation uses pinned Lean 4.34.0-rc2,
Node 24.13.0 and the authorized serial local runner.

Compound Boolean expressions inside mixed propositions, standalone negation of
local Boolean propositions, broader annotations and full-dialect compiler
correctness remain subsequent work.
