# Local helpers around Boolean-to-word loops

Candidate `2c422bd1775a5de3e866e5296af96ad3f17221c4` admits pure local helpers around Boolean-to-word loops.
Helpers support word and Boolean inputs/results, multiple word arguments,
Unit/PUnit prefixes and recursively retained standard Id input annotations.
Both used and unused helper bodies are checked. Captures preserve their values
through the loop, and calls may supply bounds, initial values, steps and results.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 209,904 native/IR comparisons, 112,896 invalid-input checks and 14,976 controls.
- Prior tests pass 161,280 comparisons, 113,664 invalid-input checks and 8,448 controls.
- The full native corpus contains 1337 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks and retained failures.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Outer word conditionals, multiple loops, broader helper/proposition
bodies and full-dialect correctness remain open.
