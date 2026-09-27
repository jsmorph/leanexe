# Multiple word arguments on helpers before Boolean loops

Candidate `4de2ae54db849935dc59a3e6e35018313b704247` admits local helpers with two or more UInt64 arguments
before Boolean-result loops. Larger arities use a shared checked function shape.
Helpers may capture prior values and functions and retain standard Id results.
Unused bodies are checked; argument order and captured values are preserved for
every loop state.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 24,432 native/IR comparisons, 20,736 invalid-input checks and 1,728 unused helper controls.
- Prior tests pass 97,008 comparisons, 82,944 invalid-input checks and 6,912 controls.
- The full native corpus contains 1206 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records successful checks and failed proof attempts.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Other helper forms, loop-containing continuations, broader helper and
proposition bodies, and full-dialect compiler correctness remain open.
