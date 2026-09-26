# Pure Id do operations

Candidate `140ce818` extends the general compiler theorem to standard `Id.run`,
`Pure.pure` and `Bind.bind` operations over UInt64 values. Their complete standard
Id instance expressions are checked. Source binds evaluate their value before
their continuation; pure extraction preserves the result by substitution.
Straight-line `let mut` updates reuse shadowing-let support. Branches admit both
`UInt64` and `Id UInt64` result-type spellings, covering early returns, nested
blocks and branch-local binds.

The following checks passed with the pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized local
serial `tools/leanrun` execution:

- `tools/arithmetic-check.js proof`: general source-to-exact-byte correctness,
  full module validation, exported invocation and all nine axiom audits.
- `tools/arithmetic-check.js engine`: actual compiler admission/reserved-export
  checks and 339 matching native Lean/V8 results across twenty-seven declarations.
  The seven new emitted modules and all native expected results are retained.

Custom Pure/Bind instance expressions are rejected, as are local continuation
functions introduced by some branch-and-continue forms. Those functions need a
separate increment; this checkpoint does not claim every Id do program. General
monads, effects and loops remain outside the current source grammar.

This increment changes source recognition and preservation. The existing backend
closure properties carry it through the same WebAssembly byte/validation proofs.
Unchanged dependency builds were reused. Neither the fixed arithmetic archive
nor the independent type-safety/runtime suites were rebuilt.
