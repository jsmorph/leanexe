# Let reduction in decision arguments

Candidate `d326ab011ecbdea4312f4f4938774c7ab634b326` admits retained and let-reduced proposition arguments
in standard conjunction and disjunction decisions. A proved source relation
records each allowed reduction prefix. The original runtime condition preserves
its bindings and checks every used and unused value.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 96,948 native/IR comparisons, 50,720 invalid-input checks and 2,336 controls.
- Prior tests pass 103,336 comparisons, 63,969 invalid-input checks and 2,368 controls.
- The full native corpus contains 1026 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) and logs preserve proof attempts and validation results.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Standalone negation of local Boolean propositions, broader annotations
and full-dialect compiler correctness remain subsequent work.
