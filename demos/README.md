# Demonstrations

The demonstrations are independently inspectable examples of prose-to-Lean-to-WebAssembly generation and exact-artifact verification.  Each directory retains its request, formal specification, generated source, executable artifact, direct artifact proof, samples, and an account of the result.  Later demos also retain controlled proof-generation experiments over fixed artifacts.

| Demo | Program | Verification role |
|------|---------|-------------------|
| [Demo 1](demo-1/README.md) | Count prime factors with multiplicity for one input value. | Original end-to-end walkthrough and early proof-kit experiments. |
| [Demo 2](demo-2/README.md) | Search ten fixed key-value pairs for the first matching key. | Fixed-size scan and two-word result baseline. |
| [Demo 3](demo-3/README.md) | Follow a search path through a fixed seven-node binary tree. | Nested comparison-tree and structured-input proof. |
| [Demo 4](demo-4/README.md) | Add one to every element of an array of at most eight words. | Held-out array-map and whole-wrapper composition test. |
| [Demo 5](demo-5/README.md) | Retain values below 100 from an array of at most eight words. | Value-dependent array-filter and output-length test. |
| [Demo 6](demo-6/README.md) | Compute `gcd(x, 42)` through an imperative scalar loop. | Held-out scalar post-test and structured-LTG test. |
| [Demo 7](demo-7/README.md) | Preserve a singleton by transferring a decrementing counter into an incrementing counter. | Checked scalar summary and deterministic-starter series. |
| [Demo 8](demo-8/README.md) | Preserve a singleton through a three-accumulator counter loop. | Out-of-sample scalar-layout transfer test. |
| [Demo 9](demo-9/README.md) | Fold a bounded array with wrapping addition. | Array-fold annotations, structured tactics, and composition boundaries. |
| [Demo 10](demo-10/README.md) | Fold a bounded array with wrapping multiplication. | Cross-operation transfer for fold support. |
| [Demo 11](demo-11/README.md) | Fold a bounded array with bitwise XOR. | Held-out residual-goal retrieval and frame-accessor test. |

The root proof package in a demo records the representative end-to-end result, while an `experiments/` directory preserves later fixed-artifact comparisons.  An experiment package may retain a slower proof because its journal establishes retrieval, transfer, or a useful failure boundary.  Each demo README identifies its primary result and explains every retained experiment stored beside it.

Benchmark distributions and rejected or censored proof-generation trials live under the [benchmark archive](../benchmarks/README.md).  Shared proof assets and retrieval metadata live under the [structured LTG catalog](../ltg/README.md).  The [verification guide](../docs/verifying.md) defines the theorem boundary and independent package check used by these demos.
