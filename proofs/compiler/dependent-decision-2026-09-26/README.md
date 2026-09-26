# Dependent conditional decision equivalence

Candidate `719cf084102d3c451932c8c1a462b0a44aa4d30f` admits proved-equivalent annotated arithmetic operands
in dependent scalar and loop-step guards. `DecidedGuard` retains the original
guard tree, original decision expression and independent `GuardDecision` witness.
Both proof-lambda domains remain exact, and both branch contexts retain the
erased proof binder for correct access to outer variables and captured helpers.

Validation uses pinned Lean 4.34.0-rc2 and Node 24.13.0 with authorized serial
local execution through `tools/leanrun`:

- `tools/arithmetic-check.js proof`: the general source-to-WASM theorem and all
  fourteen axiom audits pass, covering exact decoding, module validation and
  execution to the source result in the pinned Wasm model.
- `tools/arithmetic-check.js subset-engine dependent-decision`: 1,035 native
  Lean/V8 comparisons pass across 62 declarations, including eighteen range
  declarations. All 54 prior modules retain identical bytes.
- New focused tests pass 468 native/IR comparisons and 264 invalid-input tests,
  including checks of proof-binder domains, nested scopes, captured helpers,
  Id actions, compound conditions and loop exits.
- The preceding dependent-if and compound-syntax fixtures pass 304 and 336
  comparisons, with eight and 144 rejection tests respectively.
- The full native fixture contains 702 declarations; the emitted-Wasm check
  covers the selected 62.

The [journal](journal.md) describes source representation and proof construction.
[verification.json](verification.json) records the candidate, commands, source
hashes, exact modules and execution scope. Focused parser, scalar, step and source
equivalence proof logs accompany the complete proof and execution results.

Saved decisions and Boolean-result proposition choices still require identical
condition/decision operands. Full LeanExe dialect compiler correctness remains
unfinished.
