# Reusable Boolean-input predicates with converted calls

Candidate `b052b0de10060c12462fee2294e1295a4c8e86d9` admits reusable Bool-to-Bool helpers
in scalar expressions when their calls are converted with Bool.toUInt64. Source
and compiled bindings distinguish Boolean-input functions from word-input
predicates. Captures, repeated calls, nested closures, shadowing, standard Id
result annotations, dependent choices and unused bodies retain typed evaluation.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 1,105 inputs across 62 declarations, including 25 ranges.
- All 51 previous modules retain identical bytes.
- Focused tests pass 2,156 native/IR comparisons and 2,304 invalid-input checks.
- Prior tests pass 1,466 comparisons and 880 invalid-input checks.
- The full native corpus contains 780 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Direct Boolean-context calls and these helper declarations in step/outer-loop
scopes remain subsequent work. Full dialect compiler correctness is unfinished.
