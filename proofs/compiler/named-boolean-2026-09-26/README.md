# Directly applied named Boolean helpers

Candidate `b38a0ab0eb09544ea6b3ca79dd26555c4a4f8b4f` admits a named local Boolean helper when
its binding body applies it directly to one argument. Inputs may be UInt64 or
Bool, including standard Id input/result annotations. The source retains exact
binder annotations. Proved binder removal preserves outer captures and rejects
arguments that reference the helper itself.

Validation uses pinned Lean 4.34.0-rc2 and Node 24.13.0 through the authorized
serial local runner:

- The general source-to-WASM theorem and all sixteen axiom audits pass,
  covering decoding, module validation and execution in the pinned Wasm model.
- Native Lean/V8 agree on 1,587 inputs across 95 declarations, including
  27 range declarations. All 84 prior modules retain identical bytes.
- New focused tests pass 2,200 native/IR comparisons and 720 invalid-input
  checks. Previous fixtures pass 1,496 comparisons and 316 rejections.
- Native fixtures assert that elaboration retains the named helper application.
- The full native fixture contains 735 declarations; the Wasm check covers
  the selected 95.

[verification.json](verification.json) records commands, source hashes and exact
module hashes. The [journal](journal.md) explains representation and proof work.
Proof logs, focused tests, native outputs and exact emitted modules are retained.

Repeated calls from an arbitrary enclosing body remain subsequent work.
Full LeanExe dialect compiler correctness remains unfinished.
