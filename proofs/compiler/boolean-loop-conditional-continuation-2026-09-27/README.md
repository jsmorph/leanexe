# Conditional calls to local Boolean loop functions

Candidate `cfd9b11a303254fd81bd5510cf59abe9603edaa4` admits conditions selecting calls to local Boolean-result
loop functions, including standard Id forwarding and nested conditions. Conditions
and evidence retain their outer references; branches retain the helper binding.
Both branches are checked. The saved conditional-do failure now passes.

- The general source-to-WASM theorem and nineteen axiom audits pass.
- Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges.
- Eighteen prior modules retain identical bytes.
- Focused tests pass 97,008 native/IR comparisons, 46,080 invalid-input checks and 2,304 binding controls.
- Prior tests pass 96,768 comparisons, 78,336 invalid-input checks and 5,760 controls.
- The full native corpus contains 1276 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof and execution checks. Raw tests compare
public and direct extraction with equivalent ordinary argument bindings.
Validation uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local
runner. Saved-result bindings and wrappers around conditional calls, broader
helper/proposition bodies and full-dialect compiler correctness remain open.
