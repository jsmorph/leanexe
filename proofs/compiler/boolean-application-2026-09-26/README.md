# Immediate Boolean lambda applications

Candidate `7a00be913c3b7b438ff11cd3daf589c653d28850` admits immediate Boolean-producing lambda
applications with UInt64 or Bool arguments, including accepted Id annotations.
The source representation retains exact binders and uses typed lexical binding
evaluation. Captures and nested applications compose through scalar code,
Id actions and range steps, including break and continue.

Validation uses pinned Lean 4.34.0-rc2 and Node 24.13.0 through the authorized
serial local runner:

- The general source-to-WASM theorem and all fourteen axiom audits pass,
  covering decoding, module validation and execution in the pinned Wasm model.
- Native Lean/V8 agree on 1,403 inputs across 84 declarations, including
  24 range declarations. All 73 prior modules retain identical bytes.
- New focused tests pass 1,192 native/IR comparisons and 216 invalid-input
  checks. Three previous fixtures pass 792 comparisons and 168 rejections.
- Native examples check that elaboration retains lambda applications.
- The full native fixture contains 724 declarations; the Wasm check covers
  the selected 84.

[verification.json](verification.json) records commands, source hashes and exact
module hashes. The [journal](journal.md) explains representation, proof reuse
and fixture corrections. Proof logs, focused tests, native outputs and exact
emitted modules are retained here.

Named Boolean helper bindings and calls remain subsequent work. Full LeanExe
dialect compiler correctness remains unfinished.
