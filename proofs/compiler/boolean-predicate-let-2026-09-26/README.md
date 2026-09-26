# Direct scalar Boolean lets

Candidate `4a7b047cf91ac6eb0a0493017d25a763ece9e73e` admits scalar Boolean lets bound to Bool-input predicate
calls, including nested calls, negation, junctions, equality and choices. Captures,
shadowing and retained Id annotations preserve native values. Used and unused
bindings are checked. Scalar computations inside loops reuse this support.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 479 inputs across 28 selected declarations, including ten ranges.
- All eighteen shared modules retain identical bytes.
- Focused tests pass 16,052 native/IR comparisons and 11,468 invalid-input checks.
- Prior tests pass 33,330 comparisons and 27,913 invalid-input checks.
- Focused tests include 280 controls; prior tests include 1,468 controls.
- The full native corpus contains 864 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Direct step/outer Boolean bindings, other direct Boolean contexts and full dialect
compiler correctness remain subsequent work.
