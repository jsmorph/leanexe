# Direct Boolean helper results in scalar declarations

Candidate `d90d372690f609d5888457997e4d5e8e04d1077f` admits UInt64-to-Bool and Bool-to-Bool helper bodies
returning supported Boolean calls directly. Chained helpers, captures, wrappers,
negation and unused declarations are checked through the full converted body.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 7,348 native/IR comparisons, 5,120 invalid-input checks and 512 controls.
- Prior tests pass 13,924 comparisons, 14,748 invalid-input checks and 852 controls.
- The full native corpus contains 928 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work and invocation corrections. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Direct Boolean helper results in loop-step and outer-loop declarations, broader
annotations and full-dialect compiler correctness remain subsequent work.
