# UInt64 bindings inside converted Boolean results

Candidate `e27165c1c246d15e68dc00aa01426d9f94ad352e` admits UInt64 lets, immediate applications and named
immediate applications with Boolean bodies containing Bool-input helper calls.
Bound words preserve their type through captures, shadowing, negation and Id
annotations; both used and unused values are checked.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 7,348 native/IR comparisons, 4,608 invalid-input checks and 512 controls.
- Prior tests pass 17,200 comparisons, 10,004 invalid-input checks and 1,024 controls.
- The full native corpus contains 966 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work. Validation uses pinned Lean 4.34.0-rc2,
Node 24.13.0 and the authorized serial local runner.

Monadic binds inside converted Boolean results, broader annotations and
full-dialect compiler correctness remain subsequent work.
