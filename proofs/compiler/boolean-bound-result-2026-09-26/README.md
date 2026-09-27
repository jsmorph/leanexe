# Boolean bindings inside converted results

Candidate `7130ae58cd1131234b2cc4b20c6c5c8d9c41fcac` admits Boolean lets, immediate applications and named
immediate applications containing Bool-input helper calls in the bound value or
body. Captures, shadowing, negation, Id annotations and unused values are checked.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 7,348 native/IR comparisons, 4,096 invalid-input checks and 512 controls.
- Prior tests pass 10,350 comparisons, 6,675 invalid-input checks and 688 controls.
- The full native corpus contains 956 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work and fixture corrections. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

UInt64 bindings and monadic binds inside converted Boolean results, broader
annotations and full-dialect compiler correctness remain subsequent work.
