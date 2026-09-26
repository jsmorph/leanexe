# Beck–Fiala partitioner

## Current state

The experimental partitioner accepts at most six jobs and eight categories.  It computes assignments with exact signed fractions, Gaussian elimination, and boundary rounding.  The executable passes native Lean/WASM comparisons and independent output checks.  Its universal source-correctness and exact-binary execution theorems remain open.  The capacity limits currently restrict execution tests.  Their arithmetic and allocation sufficiency still require proofs.

Checked general lemmas establish that the protected category count is smaller than the undecided job count, a nonzero preserving direction exists, moving to the first boundary freezes a coordinate, and releasing a category with at most `t` undecided jobs gives a final discrepancy at most `2t-1`.  Checked source lemmas establish sufficient GCD fuel for every pair of `UInt64` inputs and exact fraction reduction.  Connecting these lemmas to the executable validation, elimination, and rounding loops remains work in progress.

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

The WASM entry has type `Array UInt64 → Array UInt64`.  Input words are `[n,m,k0,ids0...,k1,ids1...,...]`, where `n` counts jobs, `m` counts categories, and each `ki` precedes that job's category identifiers.  The entry checks input structure and memberships.  Output starts with a status word:

| Result | Meaning |
|--------|---------|
| `[0,t,group0,...]` | Success, computed maximum overlap, and one zero-or-one group per job. |
| `[1]` | Invalid input: missing or trailing words, invalid membership counts or identifiers, or duplicates. |
| `[2]` | The declared job or category count exceeds capacity. |
| `[3]` | Internal arithmetic, direction, or rounding-fuel failure.  Unreachability on valid inputs remains a proof obligation. |

`[0,m]` is an empty-job input when `m ≤ 8`, and returns `[0,0]`.  Jobs with no memberships enter group one.  Their maximum overlap is zero, and every category count is zero.  Header-capacity rejection precedes membership validation.  The JSON runner also rejects malformed JSON and numbers that are negative or outside JavaScript's exact-integer range before constructing input words.

## Proof development

The source and mathematical lemmas check with:

```sh
tools/leanrun --timeout 180 lake -d proofs/talos/lean build Project.Beck.SourceChecks
```

The artifact generator checks the compiler-produced WAT and writes the Talos execution model and annotation equalities:

```sh
tools/talos-artifact.js prepare beck
```

The registration remains incomplete.  An exact-binary package and a universal theorem connecting the current executable to the discrepancy bound have not been completed.  The [development plan](../plans/beck.md) records the remaining proof gates and the proposed arithmetic simplification.

The current generated annotation module fails its GCD-loop equality check: the shared scalar-loop proof representation omits result-type metadata present in the decoded instructions.  The [development journal](../devnotes.md) records the failure and its cause.
