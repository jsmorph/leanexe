# Quantized GPT-2 evaluation

The [evaluation manifest](evaluation.json) fixes the pretrained checkpoint, FP32 binary, 128-prefix sequence, three retained completion cases, and six held-out prompts.  It records the approved quantization rules from the [implementation plan](../../plans/gpt2-quantized.md).  The first quantized candidate has now been evaluated on all nine completion cases.  Subsequent designs must identify those prompts as previously evaluated.

The group64 implementation on `gpt2-quantized` has complete execution and exact-binary proofs, retained runtime and memory measurements, generated texts, and conditional numerical bounds.  The final aggregate source and artifact checks passed in the existing checkout on 2026-09-24, along with the complete execution, WAT/binary comparison, and conformance suites.  Quantized inference remains opt-in.

## Scalar projection measurements

The [kernel manifest](kernels/manifest.json) records four checkpoint projections evaluated on the FP32 model's activations for the retained first token, `Once`.  The [resident-session measurements](kernels/wasm-benchmark.json) record seven timed calls per variant after a reference comparison and two warmup calls.  Timing includes the host round trip, activation quantization, projection, and output release.  It excludes weight loading and validation.  All output bytes match their respective serial FP32 or quantized references.

| Projection | Quantized median | FP32 output-major median | Ratio |
|------------|-----------------:|-------------------------:|------:|
| QKV, 768 × 2304 | 2.544 ms | 10.394 ms | 4.09 |
| Feed-forward expansion, 768 × 3072 | 3.355 ms | 13.699 ms | 4.08 |
| Feed-forward reduction, 3072 × 768 | 3.330 ms | 13.831 ms | 4.15 |
| Vocabulary, 768 × 50257 | 53.356 ms | 227.424 ms | 4.26 |

The FP32 comparison implements the same serial reduction in input-major and output-major layouts.  The record contains both timings.  The quantized binary is `de0f34ec5a1c97a54f39c7664071278301923aebc663100fcc1002182ef9ab7a`.  Its [exact-binary proof](../../proofs/talos/lean/Project/Gpt2QuantizedLinearRows/README.md) and independent package check passed.  The measurements ran on `appledev1`, aarch64 Linux, with Wasmtime 44.0.0 and canonical NaNs.  The record includes source digests, compiler identity, CPU information, allocation counts, WASM memory, and process peak resident memory.

The maximum absolute output differences from serial FP32 were 0.05165, 0.12086, 0.81570, and 1.95932, respectively.  Each projection received its original FP32 input.  These measurements do not include accumulated quantization error through the full model, cached inference, or generated-text comparisons.

```sh
training/gpt2/.venv/bin/python training/gpt2/quantized.py export-kernels
training/gpt2/.venv/bin/python training/gpt2/benchmark_quantized.py
```

The commands use the existing Python environment and pinned checkpoint.  Generated tensor files remain under `build/gpt2-124m/quantized-kernels`.

## Original per-row cached candidate

The [model manifest](model-manifest.json) records a 127,695,972-byte checkpoint, including its header and scales.  The FP32 file contains 497,759,232 bytes.  Quantization reduces file storage by 74.3%.

The [128-prefix test](candidates/4fab215a51e58996b78dc3b988182eadcf47532f60556db7dd5d8d35468483ac/cached-test.json) uses the retained [27,638-byte candidate](candidates/4fab215a51e58996b78dc3b988182eadcf47532f60556db7dd5d8d35468483ac/program.wasm).  All 6,432,896 logits and every complete cache match the independent quantized reference bit for bit.  The reference preserves each serial FP32 reduction and the specified polynomial approximations.  The complete-model execution and exact-binary proofs remain open.

| Measurement | Quantized | FP32 |
|-------------|----------:|-----:|
| Weight file | 127,695,972 bytes | 497,759,232 bytes |
| Median token call in the prefix trace | 202.7 ms | 775.6 ms |
| Linear memory at position 128 | 737,673,216 bytes | 1,107,361,792 bytes |
| Live allocations after each token | 2 | 2 |

The token timings include host calls, logit transfer, and temporary release.  They exclude loading and validation.  These are medians across the 128 changing contexts in one trace.  Repeated warm timing runs remain pending.  The unchanged cache-copy allocation policy accounts for much of the growth in linear-memory capacity.

Greedy choices match FP32 on 87 of 128 fixed prefixes.  The largest absolute logit difference is 154.185 at prefix 57.  At that prefix, the mean difference is 140.463, the RMS difference after subtracting that mean is 1.677, and the greedy choice agrees.  Across all prefixes, the largest centered RMS difference is 1.862.  The median FP32-to-quantized KL divergence is 0.507 nats, with maximum 4.182.

The [completion comparison](candidates/4fab215a51e58996b78dc3b988182eadcf47532f60556db7dd5d8d35468483ac/completions.json) retains seven greedy and two sampled cases.  All nine differ from FP32 within the first three generated tokens.  Several quantized continuations repeat phrases or produce broken fragments.  The first sampled continuation contains “the first of the the Pisa, will to the that a the the”, while the corresponding FP32 continuation describes a village.  Sampled cases use the same recorded draws from the existing Lean PRNG.  The record includes complete texts and token IDs, including repetitive FP32 completions.  Output-quality acceptance remains undecided.

The session tests cover header and model rejection, token and cache-shape rejection, numerical failure after allocations at three transformer depths, prior-cache preservation, reset, and close.  Closing the 128-token session freed all 45,569 allocations.

```sh
training/gpt2/.venv/bin/python training/gpt2/quantized.py export-model
cp data/gpt2-quantized-v1/candidates/4fab215a51e58996b78dc3b988182eadcf47532f60556db7dd5d8d35468483ac/program.wasm build/gpt2-quantized-session.wasm
training/gpt2/.venv/bin/python training/gpt2/test_quantized_session.py build/gpt2-quantized-session.wasm build/gpt2-124m/quantized/weights.bin
training/gpt2/.venv/bin/python training/gpt2/test_quantized_model.py
tools/leanrun --timeout 60s lake build LeanExe.Examples.Prng
tools/leanrun --timeout 60s .lake/build/bin/lean-wasm compile --module LeanExe.Examples.Prng --entry LeanExe.Examples.Prng.generate --out build/prng/prng.wasm
training/gpt2/.venv/bin/python training/gpt2/compare_quantized_text.py
```

## Projection error diagnosis

The [projection diagnostics](projection-errors.json) evaluate all 49 learned projections at each of the first nine fixed prefixes.  A separate FP32 reference supplies the original inputs and matches the frozen FP32 binary's logits bit for bit.  For each input, the diagnostic compares activation-only reconstruction, weight-only reconstruction, and the approved integer projection with the original serial FP32 projection.  These measurements isolate local errors without propagating them through a modified model.

The vocabulary projection has the largest local RMS error at eight of the nine tested prefixes.  Its input maximum ranges from 53.4 to 198.5, while its median absolute coordinate ranges from 0.115 to 0.312.  The per-row scale rounds 79.2–95.6% of coordinates to zero.  At prefix seven, activation quantization alone produces RMS logit error 1.812, compared with 0.318 for weight quantization alone.  The corresponding integer projection has RMS error 1.839.

Transformer activations also contain outliers.  At the first prefix, block two's feed-forward expansion rounds 97.3% of its inputs to zero.  Its local activation-only output RMS error is 0.270, versus 0.022 for weight-only reconstruction.  These results identify activation quantization as a substantial error source.  They do not establish how much each layer contributes to final error or which revised scheme would meet an adoption criterion.

```sh
training/gpt2/.venv/bin/python training/gpt2/diagnose_quantized.py
```

## Activation groups of 64

The user approved the [grouped-activation experiment](../../plans/gpt2-quantized.md#accuracy-review-after-the-first-candidate).  The reference divides each projection input into groups of 64, computes a scale and integer dot product for each group, rescales each partial in FP32, and adds partials in group order before adding bias once.  Weight scales and embeddings retain their original quantized values.  A control uses the original per-row transformer projections and FP32 vocabulary activations, multiplying FP32-reconstructed quantized weights in serial order.

The [128-prefix comparison](experiments/group64/prefixes.json) gives:

| Variant | Greedy matches with FP32 | Median KL divergence | Maximum KL divergence |
|---------|------------------------:|---------------------:|----------------------:|
| Original per-row scales | 87/128 | 0.506706 | 4.182229 |
| Groups of 64 | 120/128 | 0.009023 | 0.251639 |
| Per-row scales with FP32 vocabulary activations | 120/128 | 0.003522 | 0.150031 |

The grouped maximum centered RMS logit difference is 1.052, compared with 1.862 for the original scheme.  Its largest raw difference is 49.587 at prefix 57, where the mean shift is 43.054, centered RMS difference is 0.868, and KL divergence is 0.000507 nats.  The control's improvement identifies final-projection activation quantization as a major contributor to the original distribution error on this trace.  The compiled grouped model reproduces every grouped logit vector in this reference calculation.  Its complete-model execution and exact-binary proofs now pass.

The [prompt-prefix comparison](experiments/group64/prompts.json) evaluates all 101 prefixes of the nine previously evaluated prompts:

| Variant | Greedy matches with FP32 | Median KL divergence | Maximum KL divergence |
|---------|------------------------:|---------------------:|----------------------:|
| Original per-row scales | 49/101 | 0.677073 | 3.736186 |
| Groups of 64 | 85/101 | 0.066768 | 0.244526 |
| Per-row scales with FP32 vocabulary activations | 87/101 | 0.039378 | 0.240125 |

The grouped maximum centered RMS difference is 0.866, versus 1.502 for the original scheme.  Its maximum raw difference is larger, 19.296 versus 13.893, because the grouped logits acquire a larger common shift at one prefix.  KL divergence measures the normalized distributions and excludes such common shifts.

The [grouped completions](experiments/group64/completions.json) retain all nine cases and both reference variants.  The first sampled grouped continuation describes a village and a monster, without the original candidate's repeated fragments.  The science continuation begins “to understand and test hypotheses; to guide new discoveries and develop new methods”.  All nine grouped continuations differ from FP32, first at generated positions 1, 2, 13, 4, 4, 7, 1, 2, and 1.  Several greedy outputs remain repetitive or factually wrong.  The FP32 vocabulary-activation control reproduces the FP32 code-prompt continuation exactly.  These examples support further testing of grouped scaling, while output-quality acceptance remains undecided.

### Compiled projection

The [grouped projection binary](experiments/group64/projection.wasm) contains 5,441 bytes, SHA-256 `f3aa382e2e810499b73494e9a74ed380c7ef64883e65cd286353493b74f3be8b`.  Its outputs match an independent NumPy reference byte for byte on all four checkpoint projection shapes.  The reference accumulates each group in 64-bit integers and checks the bound `64 × 127² = 1,032,256`.  The WASM implementation uses 32-bit integer accumulation and the specified FP32 partial-sum order.  Its exact-binary proof and independent package check pass.

The [projection measurements](experiments/group64/projection-benchmark.json) record seven calls after a reference comparison and two warmup calls.  All variants ran in the same runner scope with a one-core CPU quota, 4 GiB memory high, 6 GiB memory maximum, and 1 GiB swap maximum.  The runner lock excluded concurrent Lean work.  These resource limits differ from the earlier unscoped projection measurements.

| Projection | Groups of 64 median | Original per-row median | FP32 output-major median | FP32/grouped ratio |
|------------|--------------------:|------------------------:|-------------------------:|-------------------:|
| QKV | 3.428 ms | 3.475 ms | 13.674 ms | 3.99 |
| Feed-forward expansion | 5.311 ms | 5.365 ms | 21.465 ms | 4.04 |
| Feed-forward reduction | 5.225 ms | 4.626 ms | 20.422 ms | 3.91 |
| Vocabulary | 77.938 ms | 78.903 ms | 303.692 ms | 3.90 |

The feed-forward reduction costs 12.9% more than the original scheme in this run.  The other three median differences are about 1%, within the observed variation.  Grouping leaves the quantized weight file unchanged and uses larger temporary activation-scale arrays.  Linear-memory capacity matches the original projection in all four cases.  Each grouped call allocates three buffers and releases all three after output consumption.  Every session releases its two input buffers at close.

### Reproduction

```sh
training/gpt2/.venv/bin/python training/gpt2/experiment_grouped.py
training/gpt2/.venv/bin/python training/gpt2/experiment_grouped.py --prompts --output build/gpt2-124m/quantized/group64-prompts.json
training/gpt2/.venv/bin/python training/gpt2/compare_grouped_text.py
tools/leanrun --timeout 3m lake build lean-wasm LeanExe.Models.Gpt2.Quantized.Grouped
tools/leanrun --timeout 90s .lake/build/bin/lean-wasm compile --module LeanExe.Models.Gpt2.Quantized.Grouped --entry LeanExe.Models.Gpt2.Quantized.linearGroupedRows --out build/gpt2-124m/quantized-kernels/group64.wasm
tools/leanrun --timeout 5m training/gpt2/.venv/bin/python training/gpt2/benchmark_grouped.py
```

## Grouped cached candidate

The [current model record](model.json) pins the [verified 28,315-byte binary](../../proofs/artifacts/gpt2_quantized_cached/9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075/program.wasm), SHA-256 `9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075`.  The [scheme-2 checkpoint manifest](group64-manifest.json) records the same 127,695,972-byte file size and tensor payload as scheme 1.  The changed header distinguishes the grouped arithmetic.  Its weight SHA-256 is `9d60657659e502b8dae9f11c2e73583643962b42c662cb9b51aa53e8730ec314`.

The [complete prefix test](candidates/9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075/cached-test.json) compares all 6,432,896 logits and every cache bit for bit with the independent quantized reference.  Every logit vector also matches the retained grouped experiment's hash.  The [compiled completion comparison](candidates/9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075/completions.json) reproduces all nine reference token streams using the same sampling draws.

Greedy agreement is 120/128 on the fixed trace.  At position 128, linear memory is 737,673,216 bytes, compared with 1,107,361,792 bytes for FP32.  Each call retains only the weights and current cache.  Session close frees all 45,569 allocations.  Rejection and cleanup tests pass for invalid headers, the other scheme identifier, malformed parameters, invalid tokens and caches, and numerical failures after allocation.  The [complete session and exact-binary proofs](../../proofs/talos/lean/Project/Gpt2QuantizedCached/README.md) pass, including every status path, termination, allocation bounds, and buffer release.  Conditional numerical propagation and outward evaluation cover all 302 retained and held-out prefixes.  Propagated bounds are too coarse to certify a greedy margin.  Certificates from measured logits establish 232 individual choices.  The [numerical records](certificates/README.md) state the assumptions, bound sizes, and coverage.

The generation command loads the pinned binary and checks the weight and tokenizer hashes:

```sh
training/gpt2/.venv/bin/python training/gpt2/quantized.py export-model --scheme group64
tools/gpt2 --quantized --text 'Once upon a time, in a small village' --generate 32
```

Rebuild and test the candidate with:

```sh
tools/leanrun --timeout 3m lake build lean-wasm LeanExe.Models.Gpt2.Quantized.Cached
tools/leanrun --timeout 90s .lake/build/bin/lean-wasm compile --module LeanExe.Models.Gpt2.Quantized.Cached --entries LeanExe.Models.Gpt2.Quantized.validateModel,LeanExe.Models.Gpt2.Quantized.cachedStep --out build/gpt2-group64-session.wasm
training/gpt2/.venv/bin/python training/gpt2/test_quantized_session.py build/gpt2-group64-session.wasm build/gpt2-124m/quantized-group64/weights.bin
training/gpt2/.venv/bin/python training/gpt2/test_quantized_model.py --grouped --wasm build/gpt2-group64-session.wasm --output build/gpt2-124m/quantized-group64/cached-test.json
training/gpt2/.venv/bin/python training/gpt2/compare_quantized_text.py --grouped --wasm build/gpt2-group64-session.wasm --output build/gpt2-124m/quantized-group64/completions.json
tools/leanrun --timeout 20m training/gpt2/.venv/bin/python training/gpt2/benchmark_quantized_model.py --grouped --wasm build/gpt2-group64-session.wasm --repetitions 3 --output build/gpt2-124m/quantized-group64/warm-benchmark.json
```

The [controlled full-model timing record](candidates/9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075/warm-benchmark.json) contains one warmup trace and three measured 128-prefix traces.  Both models use the standard one-core scope.  Timing includes resident cached calls, logit transfer, and temporary release.  Loading, validation, reference comparisons, and hashing occur outside the timed region.

| Measurement | Grouped quantized | FP32 |
|-------------|-------------------|------|
| Median trace time | 27.286733 s | 97.935911 s |
| Observed trace range | 27.237625–27.312851 s | 97.788610–97.946842 s |
| Maximum warm linear memory | 747,110,400 bytes | 1,144,848,384 bytes |
| Peak process RSS | 759,934,976 bytes | 1,157,341,184 bytes |

The median ratio is 3.589.  Every repeated logit vector has the same hash.  Closing the grouped session frees all 182,273 allocations across the four traces.  Linear memory remains allocated until the runtime closes, so its warm maximum includes allocator reuse and growth across successive traces.
