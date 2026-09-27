# Boolean-result helpers before Boolean loops

Candidate `f0c4cd915e250b0679987e6a468dd85085f3a124` admits local UInt64-to-Bool and Bool-to-Bool helpers before Boolean
loops. Helpers can capture prior words, Boolean flags and admitted helpers. Repeated
calls may supply bounds, initial values, steps and final comparisons. Standard Id
result annotations are retained. Unused bodies are checked, and the source
function's captured values remain fixed for every loop state.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 64,752 native/IR comparisons, 55,296 invalid-input checks and 4,608 unused helper controls.
- Prior tests pass 64,752 comparisons, 55,296 invalid-input checks and 4,608 controls.
- The full native corpus contains 1186 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records the proof and execution checks. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
Retained helper input annotations and other helper shapes before Boolean loops,
loop-containing continuations, broader helper/proposition bodies and full-dialect
compiler correctness remain open.
