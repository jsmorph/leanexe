# Yielding range loops

Candidate `f4ffe0e0` completes one ascending unit-step `[:count.toNat]` loop
with one UInt64 accumulator. The proof sources were checked at `d1fbcaf7`;
the following commit adds only the required engine-fixture inventory. The
general theorem now derives correctness for successful pure or range extraction
through exact module bytes, decoding, validation and exported invocation.

The source model agrees with native Id range iteration. Its Nat index is
represented exactly up to the UInt64 stop, including the final exit comparison.
Extraction reserves accumulator/index/stop locals, and the execution proof uses
the remaining iteration count to prove termination of the emitted block/loop.
The actual annotated emitter, scratch allocation, branch encoding, parsing,
translation and validator rules are covered. All host/store states are allowed;
execution preserves the external store and returns the source result.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized local
serial `tools/leanrun` execution:

- `tools/arithmetic-check.js proof`: general correctness and all nine axiom
  audits; the runtime validator theorems still use only `propext`.
- `tools/arithmetic-check.js engine`: source admission, reserved exports and
  582 matching native Lean/V8 results across forty-one declarations.

Seven new modules and all native expected results are retained here. The 145
new comparisons cover counts 0/1/2/7/16/31, zero/high-bit/max-word accumulators,
indexed and index-free steps, step bindings and updates, conditional expressions,
lexical captures, prefix/suffix computations, and a zero-argument function.
Negative admission cases include non-unit steps, breaks and consecutive loops.
The focused source test also passed 45 native/IR comparisons during development.

The admitted loop always yields and carries one UInt64. Its index is available
through explicit `UInt64.ofNat`. General body branching, breaks, continue,
multiple/nested loops, additional accumulators and other range starts/steps are
not included. Constant stops currently require a UInt64 expression followed by
`.toNat`. Pure scalar expressions remain supported inside update expressions.

Lake reused unaffected dependencies. One combined focused build reached its
time limit after completing the function-byte proof; the remaining validation
target then completed separately. The fixed arithmetic source archive and
unrelated independent type-safety/runtime suites were not rebuilt.
