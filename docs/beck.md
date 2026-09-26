# Beck–Fiala partitioner

## Current state

The experimental partitioner accepts at most six jobs and eight categories.  It constructs integer cofactor directions and rounds coordinates with a shared denominator.  The executable passes native Lean/WASM comparisons and independent output checks.  The output-correctness theorem covers every input accepted by the parser.  Input validation establishes binary incidence entries, at most six jobs and eight categories, and an overlap equal to the maximum parsed row count.  Validation accepts exactly the well-formed membership encodings within capacity.  Allocation bounds and exact-binary execution remain open.

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

The checked WASM helper proofs cover structure accessors, sign and magnitude, boundary distance, frozen-coordinate reads, the all-frozen scan, array membership search, and the free-column search.  The scan theorems prove termination, source agreement, and store preservation from the array representations.  The free-column theorem also establishes the source's deterministic first-match behavior.  These execution proofs check with:

```sh
tools/leanrun --timeout 180 lake -d proofs/talos/lean build Project.Beck.ExecutionChecks
```

The artifact generator checks the compiler-produced WAT and writes the Talos execution model and annotation equalities:

```sh
tools/talos-artifact.js prepare beck
```

The registration remains incomplete.  An exact-binary package and a universal theorem connecting the current executable to the discrepancy bound have not been completed.  The [development plan](../plans/beck.md) records the remaining proof gates and the approved arithmetic design.

The generated annotation equalities pass after correcting result-type metadata in the shared scalar-loop proof representation.  The [development journal](../devnotes.md) records the original failure, its cause, and checks on two other artifacts.
