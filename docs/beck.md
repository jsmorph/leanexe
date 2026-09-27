# Beck–Fiala partitioner

The partitioner splits jobs with overlapping categories between two groups.  If each job belongs to at most `t ≥ 1` categories, the required difference between each category's group counts is at most `2t-1`.

The executable uses exact multiword integers and fraction-free elimination.  Its complete source and exact-WASM correctness proof remains in progress.  The current parser's address check bounds the incidence array, but a sufficient bound for the whole computation remains to prove.

## Build and run

The [development guide](../DEVELOPING.md#prerequisites) lists the required tools.  From the repository root:

```sh
tools/beck.js data/beck/exact-overlap.json
node test/beck.js
node test/beck.js --memory
```

The runner builds `LeanExe.Examples.BeckExact.compute`, compiles it to `build/beck/beck.wasm`, and records its identity in `build/beck/manifest.json`.  It runs WASM through the repository's Wasmtime host and prints assignments and independently recomputed category counts.  Binary hashes appear in metadata.

Input JSON has the form:

```json
{"categories": 3, "jobs": [[0, 1], [1, 2], [0, 2], [0, 1]]}
```

Category identifiers range from zero through `categories-1`.  Memberships within one job must be distinct.  Empty jobs and unused categories are allowed.  Empty input produces no assignments.  With zero overlap, every category count is zero.  Group sizes may differ.

The word-array input is `[jobCount, categoryCount, count0, ids0..., count1, ids1..., ...]`.  Success returns `[0, overlap, groups...]`, where each group is zero or one.  Malformed input returns `[1]`, the preliminary address-limit rejection returns `[2]`, and an internal arithmetic or progress failure returns `[3]`.  Proving internal failures unreachable for every supported input remains part of the source proof.

## Browser demo

After building the binary, start the server:

```sh
tools/beck-serve.js 8091
```

The server listens on `0.0.0.0:8091`.  Scenarios include 32 jobs with three memberships each, an odd category containing 65 jobs, repeated category sets, an odd cycle, jobs without memberships, and empty input.  The page runs the binary in a worker and checks every returned assignment and category count.  It reports execution time and linear-memory extent.

The editor allows 128 jobs and 32 categories.  These are interface limits.  The sufficient computational capacity bound remains to prove.  Each worker has a 30-second timeout.  Some large inputs can exhaust WASM's four-GiB address range.

```sh
node test/beck_web.mjs
node test/beck_browser.mjs
```

The first test compares the worker with Wasmtime and checks HTTP identity, validation, and independently recomputed counts.  The second uses the installed Chromium executable and tests scenarios, edits, rejection controls, and mobile layout.

## Algorithm and proof progress

Every coordinate starts at zero with one shared positive denominator.  A category remains protected while it contains more than `t` undecided jobs.  Fraction-free elimination finds a kernel direction for the protected incidence matrix.  A deterministic free column fixes its scale.  Exact comparisons choose the first boundary hit.  A round freezes every coordinate reaching either endpoint.

The checked mathematics includes the protected-category counting argument, kernel existence, the category-release discrepancy bound, and a rounding-loop theorem over arbitrary finite job and category types.  The loop theorem requires a step preserving the cube, frozen coordinates, and protected sums while freezing an additional coordinate.  It then proves completion in at most the number of jobs.

Checked arithmetic lemmas cover limb validity, normalization, addition, subtraction, comparison, multiplication, signed operations, bit extraction, and binary long division.  Signed exact division succeeds for every valid integer pair with a nonzero divisor dividing the numerator.  The complete echelon-reduction theorem proves successful execution for arbitrary valid integer matrices with compatible dimensions.  It derives exact divisibility from a bordered-minor invariant, preserves the rational kernel, and keeps the determinant scale nonzero.  The checked back-substitution step recovers an integer solution's pivot coordinate.  Constructing that solution from the final determinant remains open.

Focused checks run through the required Lean runner:

```sh
tools/leanrun --timeout 180 lake -d proofs/talos/lean build Project.Beck.Echelon Project.Beck.BackSubstitution Project.Beck.GenericLoop
```

The remaining proof work covers complete back substitution and direction construction, the implemented rounding step, source output correctness, resource bounds, and exact-binary execution.  The [development plan](../plans/beck.md) tracks those tasks.  Earlier bounded execution proofs are retired.

## Measurements

The default test compares 609 native Lean and WASM executions.  The memory test covers eight overlapping inputs from 24 through 128 jobs.  It records the binary hash, linear-memory size, allocation counters, and elapsed time.  Linear memory grows without shrinking, so its final extent records its peak extent for the call.  The host engine uses additional memory.

For the binary identified in the [development journal](../devnotes.md#nested-loop-accumulator-release), the 32-job, 16-category fixture uses 313,131,008 bytes and the 64-job fixture uses 2,021,392,384 bytes.  A preserved 256-job, four-category fixture exhausted the four-GiB address range before the latest ownership correction.  Run it with `node test/beck.js --stress`.

For `p` protected categories and rank `r`, elimination uses `O(n*p*r)` integer operations per round.  Rebuilding the matrix through at most `n` rounds gives a general `O(n^4)` upper bound.  Integer widths, array copies, and allocation add costs.  The journal records the measurements and [published algorithm references](../devnotes.md#beck-comparison-exact-division-identity-and-memory-measurements).
