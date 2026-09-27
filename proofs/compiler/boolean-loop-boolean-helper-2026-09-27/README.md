# Boolean-input word helpers before Boolean loops

Candidate `fba3031e6c8cc5c2a06e8fb57b889cc0a9c30d35` admits local Bool-to-UInt64 helpers before Boolean
loops. Helpers can capture prior words, Boolean flags and Boolean-input helpers; repeated
calls may supply bounds, initial values, steps and final comparisons. Standard Id
result annotations are retained. Unused bodies are checked, and the source
function's captured values remain fixed for every loop state.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 32,496 native/IR comparisons, 27,648 invalid-input checks and 2,304 unused helper controls.
- Prior tests pass 56,688 comparisons, 51,840 invalid-input checks and 5,760 controls.
- The full native corpus contains 1176 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records the proof and execution checks. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
Boolean helper results and other helper shapes before Boolean loops,
loop-containing continuations, broader helper/proposition bodies and full-dialect
compiler correctness remain open.
