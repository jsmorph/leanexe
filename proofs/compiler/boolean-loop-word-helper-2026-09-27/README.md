# Unary word helpers before Boolean loops

Candidate `d169e2434bef81c18d2b062ccf9bc0b55a277d2f` admits local UInt64-to-UInt64 helpers before Boolean
loops. Helpers can capture prior words, Boolean flags and word helpers; repeated
calls may supply bounds, initial values, steps and final comparisons. Standard Id
result annotations are retained. Unused bodies are checked, and the source
function's captured values remain fixed for every loop state.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 32,496 native/IR comparisons, 27,648 invalid-input checks and 2,304 unused helper controls.
- Prior tests pass 202,104 comparisons, 161,667 invalid-input checks and 16,320 controls.
- The full native corpus contains 1166 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records the proof and execution checks. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner. Outer
Boolean helper inputs/results and other helper shapes before Boolean loops,
loop-containing continuations, broader helper/proposition bodies and full-dialect
compiler correctness remain open.
