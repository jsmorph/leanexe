# Reusable UInt64-to-Bool local helpers

Candidate `6fd70bc77b1abd153ee476812e0df388919a49fb` admits repeated calls to local
UInt64-to-Bool helpers within arbitrary supported scalar expressions. Captured
words, flags and functions retain their lexical meanings. Predicate functions
have a separate source and compiler binding kind. Source evaluation and support
are defined independently of compilation. Every body and argument is checked,
including unused ones.

Validation uses pinned Lean 4.34.0-rc2 and Node 24.13.0 through the authorized
serial local runner:

- The general source-to-WASM theorem and all sixteen axiom audits pass,
  covering decoding, module validation and execution in the pinned Wasm model.
- Native Lean/V8 agree on 1,727 inputs across 105 declarations, including
  27 range declarations. All 95 prior modules retain identical bytes.
- New focused tests pass 1,148 native/IR comparisons and 864 invalid-input
  checks. Previous named-helper tests pass 2,200 comparisons and 720 rejections.
- The full native fixture contains 745 declarations; the Wasm check covers
  the selected 105.

[verification.json](verification.json) records commands, source hashes and exact
module hashes. The [journal](journal.md) explains the environment, lowering and
proof changes. Proof logs, focused tests, native outputs and exact emitted
modules are retained.

Reusable predicate declarations in loop-step or outer-loop scopes, broader
helper signatures, and full LeanExe dialect correctness remain subsequent work.
