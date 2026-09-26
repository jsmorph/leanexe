# Boolean-input predicates inside loop steps

Candidate `2cbd207c46fba092f7e33f15436a42ae55f1ed59` admits reusable Bool-to-Bool helper declarations
inside loop-step bodies. Converted calls preserve typed arguments, lexical
captures and captured values across accumulator updates. Break, continue,
nesting, Id result annotations and unused bodies use the proved source rules.

- The general source-to-WASM theorem and all eighteen axiom audits pass.
- Native Lean/V8 agree on 1,249 inputs across 68 declarations, including 31 ranges.
- All 62 previous modules retain identical bytes.
- Focused tests pass 3,600 native/IR comparisons and 2,304 invalid-input checks.
- Prior tests pass 4,028 comparisons and 3,168 invalid-input checks.
- The full native corpus contains 786 declarations.

[verification.json](verification.json) records commands, source and module hashes.
The [journal](journal.md) records the proof work. Validation uses pinned Lean
4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Declarations before a loop and direct Boolean-context calls remain subsequent
work. Full dialect compiler correctness is unfinished.
