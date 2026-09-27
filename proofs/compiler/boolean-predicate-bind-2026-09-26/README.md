# Scalar Boolean do bindings

Candidate `0f4e8fc8f1d7cdc64f149af0c1d2afc54905feb4` admits Bool-input predicate calls in Boolean actions
with scalar continuations. Direct actions and standard pure/Id.run/metadata
wrappers are recursively checked, including unused results. Bindings preserve
captures and shadowing and can appear in scalar calculations inside loops.

- The general source-to-WASM theorem and eighteen axiom audits pass.
- Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges.
- Eighteen shared modules retain identical bytes.
- Focused tests pass 8,244 native/IR comparisons, 9,216 invalid-input checks and 672 controls.
- Prior tests pass 6,468 comparisons, 5,608 invalid-input checks and 422 controls.
- The full native corpus contains 910 declarations.

[verification.json](verification.json) records commands, source hashes and modules.
The [journal](journal.md) records proof work and retained diagnostics. Validation
uses pinned Lean 4.34.0-rc2, Node 24.13.0 and the authorized serial local runner.

Boolean bind continuations that are loop steps or contain a loop, direct Boolean
helper results and full-dialect compiler correctness remain subsequent work.
