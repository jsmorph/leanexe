# Finite-arity local step-result helpers

Candidate `87a042ad` admits local helpers with any finite positive number
of UInt64 parameters returning complete ForInStep UInt64 results, including
retained Id wrappers. Shared parameter and call syntax preserves exact argument
counts, source order and lexical captures. Scalar and step-result closures retain
distinct binding kinds. Every supplied operand and every unused helper body is
checked. Source totality, extraction acceptance and support, correctness and
both compiled output invariants cover the new definitions and calls.

Both final commands exited 0 under pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: general compiler correctness, exact bytes,
  full module validation and exported execution, with all nine axiom audits.
- `tools/arithmetic-check.js subset-engine step-finite-arity`: admission, reserved
  exports and 609 matching native Lean/V8 results across 28 declarations.

Ten new range declarations cover three through six parameters, asymmetric
argument order, capturing/shadowing, nested/chained helpers, scalar helpers
inside step helpers, monadic result bindings, unused bodies and retained Id
layers. Cases exercise yielding and early stopping. All 240 focused native
Lean/IR comparisons pass. Four declaration rejection tests cover unsupported
unused bodies, wrong parameter domains, partial application and unsupported
ignored operands. Two raw syntax tests reject insufficient/excessive argument
counts. The preceding step-helper test also passes 264 comparisons and four
rejection tests; its former three-argument rejection is now a positive case.

All 28 modules and expected results are retained with sizes and SHA-256 hashes
in verification.json. Eighteen selected preceding modules kept identical bytes.
This was a focused execution run; the full corpus now contains 319 declarations.
The preceding full 259-declaration execution evidence remains in
../extrema-2026-09-25. General type validation used cached dependencies. No
backend/runtime operation changed; unrelated suites and the fixed arithmetic
archive were not rebuilt. Pattern matching on complete step results, multiple
loops and additional accumulators remain separate capabilities.
