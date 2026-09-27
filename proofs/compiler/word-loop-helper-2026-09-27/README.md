# Local helpers around word-result conditional loops

Candidate `a222486a9f47fecca7494381bda345aa01f89b11` admits pure local helpers before word-result conditional
loops. Helpers support word/Boolean inputs and results, multiple word arguments,
Unit/PUnit prefixes and recursively retained Id input annotations. Captures and
argument order are preserved; used and unused helper bodies are checked.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 209,904 native/IR comparisons, 112,896 invalid-input checks and 14,976 controls.
- Prior tests pass 338,688 comparisons, 186,624 invalid-input checks and 21,120 controls.
- The full native corpus contains 1367 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks. Validation uses
pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.
Broader Boolean helper/proposition bodies, general local loop-function calls,
multiple loops, retained instances, broader signatures and full-dialect
correctness remain open.
