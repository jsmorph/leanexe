# Boolean-input predicate choices over propositional guards

Candidate `5ddec22c044ad05c3516a67e842e0b5cc3481016` admits Boolean-valued ordinary and dependent choices
whose conditions are UInt64 comparisons, propositional literals, negation or
junctions of admitted guards. Converted calls can supply the guard's word
operands. Both branches are checked; execution uses the selected branch.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 555 inputs across 32 selected declarations, including twelve ranges.
- All eighteen shared modules retain identical bytes.
- Focused tests pass 16,052 native/IR comparisons and 11,670 invalid-input checks.
- Prior tests pass 16,356 comparisons and 11,640 invalid-input checks.
- Both test groups include twelve admission controls.
- The full native corpus contains 854 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Direct Boolean contexts, saved Boolean variables in mixed propositional guards
and full dialect compiler correctness remain subsequent work.
