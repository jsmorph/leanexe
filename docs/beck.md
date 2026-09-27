# Beck–Fiala partitioner

## Current state

The experimental partitioner accepts at most six jobs and eight categories.  It constructs integer cofactor directions and rounds coordinates with a shared denominator.  The executable passes native Lean/WASM comparisons and independent output checks.  The output-correctness theorem covers every input accepted by the parser.  Input validation establishes binary incidence entries, at most six jobs and eight categories, and an overlap equal to the maximum parsed row count.  Validation accepts exactly the well-formed membership encodings within capacity.  The universal WASM execution theorem proves termination, agreement with the source result, and sufficient allocation under explicit heap and memory assumptions.  Independent exact-binary package verification remains open.

Source proofs establish that the executable constructs a nonzero direction preserving every protected category, gives frozen jobs zero direction, and bounds every coefficient's magnitude by 120.  The boundary scan chooses the first minimum boundary ratio using exact word-sized products.  A round preserves coordinate bounds and protected category sums, keeps frozen jobs fixed, and freezes an additional job.  Starting from zero, the full rounding loop finishes with every job frozen, a nonzero denominator, and denominator at most `120^6`.  The release argument gives final discrepancy at most `2t-1` for positive overlap and zero discrepancy for zero overlap.  `Project.Beck.Source.compute_correct` transfers that result to the returned zero-or-one groups and the category counts specified by the encoded membership lists.  These proofs use counting, determinant bounds, Cramer's identity, a bordered-determinant identity, and interval inequalities.

## Input and execution

The runner reads a JSON file with a category count and one membership array per job.  Category identifiers range from zero through one less than the category count.  Job order determines output order.  Membership order is unrestricted, and duplicate memberships are invalid.

```json
{
  "categories": 3,
  "jobs": [[0, 1], [0, 1], [0, 2], [0, 2], [1, 2], [1, 2]]
}
```

Each job in this example belongs to two categories.  Every category contains four jobs, exceeding the discrepancy bound of three.

With the prerequisites from [Developing LeanExe](../DEVELOPING.md) installed:

```sh
tools/beck.js data/beck/overlap.json
node test/beck.js
```

The runner builds the Lean source and compiler, compiles the `compute` entry, executes the resulting WASM through the repository's Wasmtime host, and prints the assignments and independently recomputed category counts.  `WASMTIME_C_API` can select an existing Wasmtime C API installation when building the host.  The test compares native Lean with WASM and checks every successful output.  Its corpus includes every membership pattern with at most three jobs and three categories, deterministic larger samples, and malformed inputs.

The WASM entry has type `Array UInt64 → Array UInt64`.  Input words are `[n,m,k0,ids0...,k1,ids1...,...]`, where `n` counts jobs, `m` counts categories, and each `ki` precedes that job's category identifiers.  The entry checks input structure and memberships.  Every valid encoding contains at most 56 words.  Output starts with a status word:

| Result | Meaning |
|--------|---------|
| `[0,t,group0,...]` | Success, computed maximum overlap, and one zero-or-one group per job. |
| `[1]` | Invalid input: missing or trailing words, invalid membership counts or identifiers, or duplicates. |
| `[2]` | The declared job or category count exceeds capacity. |
| `[3]` | Internal arithmetic, direction, or rounding-fuel failure.  The source theorem proves this result unreachable after input validation succeeds. |

`[0,m]` is an empty-job input when `m ≤ 8`, and returns `[0,0]`.  Jobs with no memberships enter group one.  Their maximum overlap is zero, and every category count is zero.  Header-capacity rejection precedes membership validation.  The JSON runner also rejects malformed JSON and numbers that are negative or outside JavaScript's exact-integer range before constructing input words.

## Arithmetic

Rows and columns are scanned in ascending order.  The basis search extends a nonsingular minor by the first row and column with a nonzero bordered determinant.  The direction uses that minor and its column-replacement determinants.  Determinants use Laplace expansion with structurally decreasing order.

Coordinates use signed 64-bit numerators and a positive shared denominator.  Arithmetic uses two’s-complement words.  For minors of order at most five, the determinant bound is 120.  The denominator grows by at most 120 per round, reaching at most `120^6 = 2985984000000`.  The source round and loop proofs establish these bounds and exactness of the updates for every accepted input.

## Proof development

The source and mathematical lemmas check with:

```sh
tools/leanrun --timeout 180 lake -d proofs/talos/lean build Project.Beck.SourceChecks
```

The checked WASM helper proofs cover structure accessors, sign and magnitude, boundary distance and ratio scanning, frozen-coordinate reads, the all-frozen scan, array membership search, the free-column search, category live-job counts, the rejection constructor, owned-array release, array deletion, and recursive determinants.  The scan theorems prove termination, source agreement, and store preservation from the array representations.  The free-column theorem establishes the source's deterministic first-match behavior.  The category counter proves its checked indexing and count arithmetic safe within the input bounds.

The rejection constructor and array deletion use the shared allocator proof for free-list reuse and memory growth.  They establish ownership of their new arrays and preserve existing protected memory.  Deletion also proves that an out-of-bounds index returns the original array.  The determinant theorem composes row and column deletion with recursive calls and proves exact source agreement, termination, heap preservation, and sufficient allocation.  Its byte budget is at most 200,160 for order at most six.  The theorem assumes represented, protected input arrays, in-bounds selected matrix entries, and sufficient address and memory capacity.

The membership-reader theorem covers every accepted membership list within bounds.  It proves termination, source agreement, ownership of the returned incidence row, preservation of protected inputs, and a byte budget of `count*(48+8*(categories+1))`, at most 960 bytes.  It includes identifier and duplicate checks, row replacement, and release of intermediate rows.  The job-reader theorem composes those row operations with incidence concatenation and charges at most 1,520 bytes per job.  The complete accepted-input parser theorem covers header checks, initial allocations, job parsing, complete input consumption, and its returned fields.  It charges at most `112 + 1520*n` bytes.  All three parser theorems cover both owner-equals-pointer inputs and borrowed inputs with owner zero.  For positive job counts, the returned incidence owner equals its data pointer.

The protected-matrix theorem covers initial allocation, category selection, all row pushes, intermediate releases, the category loop, and final ownership cleanup.  It proves exact source agreement and charges at most `56 + 448*n*m` bytes, or 21,560 bytes within capacity.

The bordered-minor candidate theorem covers duplicate-index checks, row and column extension, determinant calculation, and the optional basis result.  It preserves the caller’s protected memory and returns fresh, disjoint owned index arrays when it succeeds.  Its budget is `208 + determinantBytes(k+1)` for an original minor of order `k`, assuming the extended minor meets the determinant theorem’s bounds.

The complete basis-extension theorem proves the nested row and column search, termination, and first-success selection.  It derives the candidate bounds from a well-formed basis and returns either the unchanged basis fields or fresh, disjoint owned index arrays.  It preserves protected memory and charges at most `(208 + determinantBytes(k+1)) * width * (matrix.size / width)` bytes.  The theorem includes the matrix-header read, guarded division, all release guards, and function entry and return.

The complete repeated-extension theorem returns the source `findBasis` result, preserves protected memory, and retains represented index arrays and fresh output ownership when the basis changes.  Its loop terminates by fuel and the stop flag.  It charges `200368 * width * (matrix.size / width) * fuel` bytes for fuel and width at most six and fewer than six matrix rows.

The complete direction theorem covers protected-matrix construction, basis search, free-column selection, initial-vector allocation, the terminating cofactor loop, and all emitted releases.  It returns an owned array equal to the source direction and preserves the caller's protected memory.  The supported-input theorem derives the matrix, rank, and free-column preconditions from the source counting and basis results whenever a live job remains.  Its allocation charge combines the search bound, two vector allocations, and one column replacement, determinant call, and vector replacement per basis column.  A conservative uniform bound is 37,290,440 bytes per direction call.

The complete round execution theorem composes direction construction, boundary selection, numerator-array construction, and cleanup.  It proves that both failure branches are unreachable on supported round states and returns the source round result with ownership, freshness, and preserved caller memory.  Its allocation charge is at most 37,291,120 bytes.

The outer-rounding theorem proves fuel-based termination, the all-frozen exit, replacement-array cleanup, and source-result agreement.  It covers distinct point owner and data pointers and charges the round bound times the supplied fuel.  The zero-fuel theorem also permits distinct incidence owner and data pointers, covering the empty-input call.  Entry fragments prove the borrowed parser call, accepted-status check, both initial zero-array allocations, and the call returning the final rounded point.  Initialization establishes ownership, disjoint allocations, preserved caller memory, and a charge of `2*(48+8*(n+1))` bytes.  The complete output branch proves header allocation, group assignment, append-loop termination, and header cleanup.  It returns the source output with ownership and freshness, preserves caller memory, and charges `72 + 120*n` bytes.  Final cleanup releases both initial coordinate arrays while retaining the result.  The complete entry theorem composes parsing, initialization, rounding, output construction, and cleanup.  Its uniform allocation bound is 223,756,952 bytes.  These execution proofs check with:

```sh
tools/leanrun --timeout 180 lake -d proofs/talos/lean build Project.Beck.ExecutionChecks
```

The artifact generator checks the compiler-produced WAT and writes the Talos execution model and annotation equalities:

```sh
tools/talos-artifact.js prepare beck
```

`Project.Beck.Spec.compute_correct` proves the complete WASM result and discrepancy bound for every valid membership encoding within capacity.  `compute_source_eq` proves exact source agreement for every accepted input.  The source-driven gate regenerates the artifact before checking both:

```sh
tools/talos-proof.js check beck
```

The caller supplies a represented input array and an allocator state satisfying `Heap.At`.  The input lies below the heap frontier and outside every free allocation.  `OutputBudget` requires the frontier plus 223,756,952 bytes and any reserved continuation budget to remain below `2^32`, fit within a page limit of at most 65,536, and stay within the modeled memory capacity.  Existing memory pages must also fit that limit.  The theorem preserves protected caller memory and returns an owned result.  The allocation charge conservatively sums all allocation requests without deducting free-list reuse.

Execution uses the pinned Talos semantics and its modeled memory-growth behavior.  The native host, Wasmtime, operating system, and physical resource availability are outside the Lean theorem.  The universal execution theorem covers valid encodings.  Rejection behavior has source proofs and executable tests.

The independent package for the 27,068-byte binary with SHA-256 `55f407d3f82b34a59e95489f2ed40ea756cb621d780f76ee48eb5a60645d080f` is under verification.  The [development plan](../plans/beck.md) records the remaining proof gate and the approved arithmetic design.

The generated annotation equalities pass after correcting result-type metadata in the shared scalar-loop proof representation.  The [development journal](../devnotes.md) records the original failure, its cause, and checks on two other artifacts.
