# Direct Boolean bindings across loop scopes

Candidate `f7909f515470ccd506a836b53e48b4855a3488b2` admits Boolean lets bound to Bool-input predicate calls
inside loop steps and before loops. Saved flags preserve captures and can control
break/continue, loop bounds and initial values, helpers and final results. The
compiler checks both used and unused bound values.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 521 inputs across 26 selected declarations, including seventeen ranges.
- All eighteen shared modules retain identical bytes.
- Focused tests pass 3,264 native/IR comparisons and 1,672 invalid-input checks.
- Prior tests pass 51,154 comparisons and 31,295 invalid-input checks.
- Focused tests include eighty controls; prior tests include 1,992 controls.
- The full native corpus contains 872 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Direct conditions, Boolean do binds, direct Boolean helper results and full
dialect compiler correctness remain subsequent work.
