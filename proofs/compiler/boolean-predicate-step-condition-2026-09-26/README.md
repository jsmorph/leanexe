# Direct loop-step Boolean conditions

Candidate `49fd39d2d303b8c913496cfd580d1d21d21aef70` admits Bool-input predicate calls in conditions that
choose a yielding or completed loop step. Ordinary and dependent branches support
truth tests and Boolean Eq/Ne. Helpers can be declared inside the step or captured
from outside the loop. Both branch values and break/continue flags are proved.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 521 inputs across 26 declarations, including seventeen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 9,408 native/IR comparisons, 5,736 invalid-input checks and 408 controls.
- Prior tests pass 7,892 comparisons, 6,894 invalid-input checks and 500 controls.
- The full native corpus contains 890 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Boolean do binds, direct Boolean helper results, broader annotations and
full-dialect compiler correctness remain subsequent work.
