# Demo 9 fold-sum benchmark

Demo 9 accepts an array of at most eight `UInt64` values and returns a singleton array containing their wrapping sum.  Inputs longer than eight produce an empty array.  Every retained run uses the same 1,979-byte WASM artifact with SHA-256 digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.

## Results

| Variant | Outcome | Stage 5 |
|---|---|---:|
| Baseline | Accepted | 3,431.870 s |
| Fold-prefix support | Accepted | 4,055.765 s |
| Fold annotation and structured LTG | Accepted | 3,188.251 s |
| Exact traversal-prefix theorem | Censored without an accepted proof | at least 4,285 s |
| Result-store LTG | Accepted; timing censored | 3,149.420 s |

The exact traversal-prefix run selected the new `fixed-array-traversal-input` entry through structured LTG and applied `FixedArrayTraversalInput.continuingProgram_spec` to the generated region equality.  That composition discharged the loop guard, indexed address, memory bound, represented-element read, and item-local update for the continuing branch.  The agent then proved the accumulator update and measure decrease, but it stalled while constructing the completed branch and final singleton result.

The censored run exceeded the fastest retained accepted run by about 1,097 seconds and the baseline by about 853 seconds.  It supplies positive evidence for theorem retrieval and structural reduction, but no accepted proof or proving-time improvement.  Its journal identifies the unannotated fold-exit and result-store suffix as the next shared proof boundary.

The result-store run received the new `fixed-array-result` entry and selected it on its first LTG query.  Its accepted 678-line proof applies `lengthStore_spec` twice, `payloadStore_spec` once, `singletonStore_at` once, and `FixedArrayTraversalInput.continuingProgram_spec` once.  Independent package verification accepted the exact behavior theorem and artifact theorem over the unchanged WASM digest.

The result-store time is excluded from timing comparisons because the journal records two broad searches of the dependency repository whose path results included external demo and benchmark proofs.  The agent reports that it opened only selected proof-kit source files and used none of the external proof paths, but the searches violated the experiment boundary.  The run remains valid evidence that structured retrieval found the result-store support and that its declarations compose with the artifact proof.

`baseline`, `fold-prefix-2`, `array-fold-annotation-1`, and `result-ltg-search-censored-1` contain independently verifiable proof packages.  `traversal-prefix-censored-1` preserves the incomplete candidate, journal, generated annotation equality, recipes, and exact task inputs from the interrupted run.  The latter directory is diagnostic evidence rather than a proof package and therefore cannot pass `tools/leanexegen verify`.
