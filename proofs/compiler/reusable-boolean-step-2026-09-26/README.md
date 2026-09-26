# Reusable predicate helpers in loop steps

Candidate `c6f609738fc095907af4c5eb44aca1c0edd39799` admits UInt64-to-Bool helper
declarations inside loop-step bodies. Repeated calls, captures, nesting and
step-valued helper captures preserve native accumulator and exit behavior.

Validation uses pinned Lean 4.34.0-rc2 and Node 24.13.0 through the authorized
serial local runner:

- The general source-to-WASM theorem and all sixteen axiom audits pass,
  covering binary decoding, module validation and formal WASM execution.
- Native Lean/V8 agree on 579 inputs across 33 declarations, including
  13 range declarations. The eleven modules shared with the preceding
  scalar-helper archive retain identical bytes.
- New focused tests pass 1,872 native/IR comparisons and 864 invalid-input
  checks. Prior scalar-helper tests pass 1,148 comparisons and 864 rejections.
- The full native corpus contains 751 declarations; this selected WASM suite
  contains the six new loops, ten scalar helpers and seventeen guard-core cases.

[verification.json](verification.json) records commands, source hashes and exact
module hashes. The [journal](journal.md) records proof work and retained diagnostics.

Predicates declared around a loop, broader helper signatures and full LeanExe
dialect compiler correctness remain subsequent work.
