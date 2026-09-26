# PUnit do-block continuations

Candidate `af86f5d8` admits the `PUnit.{1} → UInt64 → result` helper
form and `PUnit.unit.{1}` applications retained by elaborated do blocks.
A shared UnitSyntax description records the concrete type and value spelling.
The existing unit/function bindings and semantics remain shared with Unit.
Exact source patterns feed generalized acceptance, correctness, source-support
and invariant proofs for scalar functions, yielding steps, early-exit steps
and scalar helpers surrounding loops. No IR/backend operation changed.

Both function type and lambda domain must use an admitted concrete spelling.
Every body is checked, including unused bodies. Tests reject unsupported bodies
and PUnit universes outside this increment. Mixed Unit/PUnit calls work because
the two admitted literal values have the same unit meaning.

Both final commands exited 0 using pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: complete compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js subset-engine punit-continuations`: admission,
  reserved exports and 453 matching native Lean/V8 results across 24 declarations.

The fixed execution group contains twelve new declarations and twelve existing
helper/do/loop cases. Six new pure declarations cover explicit PUnit helpers,
captures, chaining, unused bodies, nested helpers and Id results. Six new range
declarations cover the generated branch-update join that exposed this gap,
explicit step helpers, scalar helpers inside loops, yielding joins, helpers
surrounding loops, continue, break and strides. All 228 focused native Lean/IR
comparisons and three rejection tests passed.

All 24 tested modules and expected results are retained with sizes and SHA-256
hashes in verification.json. The twelve selected prior modules kept identical
bytes. This was a focused execution run; the full corpus now contains 283
declarations. The preceding full 259-declaration execution evidence remains in
../extrema-2026-09-25. General type validation used cached dependencies; the
fixed arithmetic archive and unrelated runtime suite were not rebuilt.
