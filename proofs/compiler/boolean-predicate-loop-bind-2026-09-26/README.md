# Boolean do bindings across loop scopes

Candidate `7f00d92376af1e64a26da01fff4a659c522eb03c` admits Bool-input predicate actions in bindings whose
continuations are loop steps or contain a loop. Direct and standard wrapped
actions preserve captures through loop-state changes. Saved flags can control
break/continue, supply bounds and initial values, and contribute to final results.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 521 inputs across 26 declarations, including seventeen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 12,480 native/IR comparisons, 6,912 invalid-input checks and 320 controls.
- Prior tests pass 11,992 comparisons, 11,102 invalid-input checks and 790 controls.
- The full native corpus contains 918 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work. Validation uses pinned Lean 4.34.0-rc2,
Node 24.13.0 and the authorized serial local runner.

Direct Boolean helper results, broader annotations and full-dialect compiler
correctness remain subsequent work.
