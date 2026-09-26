# Predicate helpers declared around loops

Candidate `4f6244ab427cfcd4e2d024d13f521a3f1d71127d` admits reusable UInt64-to-Bool
helpers before a bounded loop. Calls may appear in bounds, initial values, loop
steps and final results. The source and compiler preserve captured values across
accumulator updates, nested helper declarations and shadowing.

Validation uses pinned Lean 4.34.0-rc2 and Node 24.13.0 through the authorized
serial local runner:

- The general source-to-WASM theorem and all sixteen axiom audits pass,
  covering binary decoding, module validation and formal WASM execution.
- Native Lean/V8 agree on 771 inputs across 41 declarations, including
  21 range declarations. All 33 previous modules retain identical bytes.
- New focused tests pass 1,920 native/IR comparisons and 864 invalid-input
  checks. Prior loop-step tests pass 1,872 comparisons and 864 rejections.
- The full native corpus contains 759 declarations; the selected WASM suite
  extends the previous 33 declarations with eight outer-predicate examples.

[verification.json](verification.json) records commands, source hashes and exact
module hashes. The [journal](journal.md) records proof work and retained diagnostics.

Broader helper signatures and full LeanExe dialect compiler correctness remain
subsequent work.
