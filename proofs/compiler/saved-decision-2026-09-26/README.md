# Saved Boolean decision equivalence

Candidate `ddb03642fd91e37d5fcfea034b0b971ff67be4cd` admits proved-equivalent arithmetic operands
in saved `decide` values and ordinary or dependent Boolean-result proposition
choices. Original source decision expressions and exact proof-lambda domains
are retained in the checked source representation.

Validation uses pinned Lean 4.34.0-rc2 and Node 24.13.0 through the authorized
serial local runner:

- The general source-to-WASM theorem and all fourteen axiom audits pass,
  covering decoding, module validation and execution in the pinned Wasm model.
- Native Lean/V8 agree on 1,219 inputs across 73 declarations, including
  21 range declarations. All 62 prior modules retain identical bytes.
- New focused tests pass 1,192 native/IR comparisons and 552 invalid-input
  checks. Three preceding fixtures pass 912 comparisons and 100 rejections.
- The full native fixture contains 713 declarations; the Wasm check covers
  the selected 73.

[verification.json](verification.json) records commands, source hashes and exact
module hashes. The [journal](journal.md) explains the source representation and
proof construction. Proof logs, focused tests, native outputs and exact emitted
modules are retained here.

Boolean-returning local helpers and full LeanExe dialect compiler correctness
remain unfinished.
