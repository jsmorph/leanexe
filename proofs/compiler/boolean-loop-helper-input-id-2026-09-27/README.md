# Retained Id helper inputs before Boolean loops

Candidate `24cd00ae7f9ab4d8dd870be27802692fcb951099` admits any number of standard Id layers on helper input
annotations, across word/Boolean input and result kinds. The declared and lambda
input domains must match. Source annotations are preserved, unused helper bodies
are checked, and captured values remain fixed for every loop state.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 64,752 native/IR comparisons, 73,728 invalid-input checks and 4,608 unused helper controls.
- Prior tests pass 64,992 comparisons, 55,296 invalid-input checks and 4,608 controls.
- The full native corpus contains 1196 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records successful checks and failed proof attempts.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Other helper forms, loop-containing continuations, broader helper and
proposition bodies, and full-dialect compiler correctness remain open.
