# Beck–Fiala partitioner

## Objective

Deliver one exact two-group partitioner with a universal source theorem, an exact-WASM execution theorem, derived resource limits, and a browser demo on port 8091.  The theorem must quantify over job count, category count, and overlap.  Weights, online operation, exact equal-size groups, and discrepancy minimization remain outside the requested scope.

## Current implementation

The approved implementation uses base-2^32 integer limbs, fraction-free elimination, a shared coordinate denominator, deterministic kernel selection, and first-boundary rounding.  The main runner, tests, and browser demo use `LeanExe.Examples.BeckExact.compute`.  The obsolete bounded binary, its generated model and execution proofs, and its registrations are removed.  Reusable source mathematics remains available.

The compiler corrections address repeated evaluation of monadic loop bodies and missing release of nested-loop accumulators.  The complete ownership test and native/WASM comparisons passed before consolidation of the runners.  The generalized program still requires a sufficient resource guard and complete execution proof.

## Remaining work

- [x] Compile and run multiword elimination through the public input interface.
- [x] Prove multiword normalization, addition, subtraction, comparison, multiplication, signed operations, and bit shifting.
- [x] Prove arbitrary-dimension rounding and integer condensation lemmas.
- [x] Prove binary long division and signed exact division.
- [x] Prove the elimination invariant and successful kernel-preserving echelon reduction.
- [x] Prove complete exact back substitution with a determinant-scaled integer kernel.
- [x] Connect protected-matrix construction and free-column availability to the direction theorem.
- [ ] Connect the implemented rounding step and parser to the universal source theorem.
- [ ] Derive sufficient indexing, arithmetic-width, fuel, and allocation bounds.
- [ ] Prove exact-WASM execution and check the independent package.
- [ ] Run native/WASM, browser, edge-case, and memory tests against that binary.

The [program guide](../docs/beck.md) gives commands and current limitations.  The [development journal](../devnotes.md) records test results, proof progress, compiler diagnoses, and the GPU algorithm investigation.
