# Verified quantized GPT-2 124M

This plan expands [phase 15 of the Development Plan](../plan.md#15-extend-gpt-2-with-quantized-inference).  The user approved implementation and the [file and session API](gpt2-quantized-format.md) on 2026-09-22.  Work runs on `gpt2-quantized`.  The scalar projection has checked execution and exact-binary proofs and retained measurements.  The grouped model has complete source-session and exact-binary proofs.  Conditional numerical propagation and evaluation are complete.  Repository proof and execution tests remain active.  On 2026-09-24, the user excluded release-record maintenance from the remaining work.

The execution milestone is a deployed WebAssembly binary that implements a specified mixed-precision GPT-2 algorithm: eight-bit weights and activations for learned linear projections, wider integer accumulation, and FP32 computation between projections.  It includes cached inference through 128 tokens, termination, allocation bounds, and buffer release.  Evaluation determines the storage reduction, execution speed, and output differences.  A subsequent milestone proves numerical error bounds and sufficient conditions for preserving greedy token choices.

## Existing implementation and constraints

The [current model](../LeanExe/Models/Gpt2/README.md) has twelve blocks, width 768, feed-forward width 3,072, and 50,257 vocabulary entries.  Its 124,439,808 FP32 parameters occupy 497,759,232 bytes.  The token embedding and vocabulary projection share one matrix.  The checkpoint retains 1,024 position rows, while execution accepts positions zero through 127.

The [cached-inference proofs](../proofs/talos/lean/Project/Gpt2CachedStep/README.md) cover the token step, the session from initialized memory, and the exact 19,083-byte binary with SHA-256 `e93de126e00d7f5c5b9b30ca014a13b1385e9f91e3cb6b4e56a4aacf7a2b4ade`.  They supply reusable FP32, packed-memory, allocation, and release results.  The inspected repository checkpoint is `a4655383ee80d3d80830b6bddfb6248a9d5c2b4b`.  Its proof workspace pins Talos `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`.

The [language specification](../docs/spec.md#numeric-semantics) supports unsigned integer words and raw-word FP32 arithmetic.  Signed integer operations, FP32 rounding to an integer, and integer/FP32 numerical conversions require compiler work.  The [binary translator](../proofs/talos/lean/Project/Artifact/Binary/Translate.lean) currently covers unsigned byte loads and the existing FP32 operations.  Additional instruction forms require corresponding decoder, validator, translation, and soundness proofs.  The [artifact format](../docs/artifact-format.md#normative-binary-profile) also requires these extensions for SIMD.

The [recorded 128-position run](../data/gpt2-124m/README.md#execution-evidence) used 1,107,361,792 bytes of WASM linear memory, including a final 9,437,184-byte cache.  Whole-block reuse leaves smaller freed cache allocations behind as the cache grows.  Weight storage, live tensors, linear-memory capacity, and process memory therefore need separate measurements and bounds.

## Approved first version

| Choice | First version | Consequence |
|--------|------------------------|-------------|
| Quantized operations | Quantize QKV, attention output, both feed-forward projections, and the vocabulary projection. | Covers the learned matrix products with reduction lengths 768 and 3,072. |
| Weight encoding | Signed bytes in `[-127, 127]`, zero point zero, one positive FP32 scale per output channel.  Store each output channel's reduction coefficients contiguously. | Requires a new packed layout and an exporter with explicit matrix orientation. |
| Activation encoding | Compute one scale for each input row at each projection, using that row's maximum absolute value.  Quantize the row once and reuse it for all output channels. | Adds a scale scan and conversion pass.  Supports changing activation ranges without a calibration dataset. |
| Shared embedding | Store one quantized token matrix with one scale per token.  Decode the selected row for embedding lookup and use the same bytes and scales for vocabulary projection. | Preserves weight sharing and avoids a second vocabulary-sized matrix.  Embedding quantization contributes to numerical error. |
| FP32 computation | Retain position embeddings, biases, LayerNorm parameters, residual streams, GELU, attention scores and weighted-value sums, softmax, cache contents, and returned logits in FP32. | The cache representation remains compatible in shape.  Its values follow the quantized recurrence. |
| Accumulation and compiler API | Use signed 32-bit accumulation.  Propose narrow raw-word operations for signed-byte decoding, integer accumulation, nearest-even rounding, and numerical conversion, following the existing FP32 API pattern. | Review the emitted instruction set and API before implementation.  The specification interprets words as mathematical integers and proves representability. |
| Failure behavior | Return an explicit status for malformed model data, invalid token/cache inputs, nonfinite quantizer inputs, or nonfinite final outputs. | Requires a specified result layout and cleanup on failures after allocation. |
| First execution target | Use scalar WASM in the existing Wasmtime host and Python environment. | Measure a complete projection before approving SIMD or another execution target. |

The output-quality criterion for adoption remains under discussion.  Performance evaluation compares repeated measurements with FP32, including quantization and allocation costs.  Dependencies and changes to the Talos pin require separate approval.

### Arithmetic definition

Let `RN32` mean binary32 rounding to nearest with ties to even, and let `RNE` round a finite real value to the nearest integer with ties to even.  For a finite row `x`, propose:

```text
a = max_i |x_i|
s = 1                                      if a = 0
s = max(2^-126, RN32(a / 127))              otherwise
r_i = RN32(x_i / s)
q_i = RNE(clamp(r_i, -127, 127))
```

Use the same rule for each weight output channel during export.  The positive normal scale floor gives defined behavior for subnormal rows.  Both signs of zero quantize to integer zero.  Clamp the quotient before converting it to an integer.  Specify each comparison, division, clamp, and conversion on raw words, including rejection of nonfinite source values.  Prove the scale and quotient properties needed by the conversion.  The format reserves byte `0x80`, which represents `-128`, and rejects it during model validation.

For a projection of reduction length `K`, define its mathematical accumulator and FP32 output by:

```text
A_j = sum_(i < K) qx_i * qw_(j,i)
t_j = RN32(sx * sw_j)
y_j = RN32(RN32(RN32(A_j) * t_j) + bias_j)
```

The vocabulary projection omits the bias addition.  `RN32(A_j)` denotes signed integer-to-FP32 conversion.  It can round: the accumulator bound exceeds `2^24`.  The source definition and execution theorem must preserve this operation order, including the separately rounded scale product.  Embedding lookup computes `RN32(qw_(token,i) * sw_token)` before the existing FP32 position addition.  The next learned projection quantizes its own FP32 input row.

For every reduction prefix `m ≤ K ≤ 3072`,

```text
|sum_(i < m) qx_i * qw_(j,i)| ≤ m * 127^2
                             ≤ 49,548,288 < 2^31.
```

Prove this bound for every prefix, signed byte decoding, each widened product, and the accumulator update.  The machine-word recurrence must agree with the integer sum at every iteration.  Any later vector implementation needs bounds for its lane and intermediate sums as well.

The [ONNX QuantizeLinear definition](https://onnx.ai/onnx/operators/onnx__QuantizeLinear.html) documents scale axes, saturation, and nearest-even rounding.  The [WebAssembly numerical specification](https://webassembly.github.io/spec/core/exec/numerics.html) defines integer interpretation, rounding, and numerical conversion.  Use these references to review conventions and instruction behavior.  The Lean definitions above determine this implementation's chosen range and sequence of operations.

### Model format and validation

Define a versioned file with checked lengths and offsets for packed matrix bytes, scale words, and retained FP32 tensors.  Fix byte order, channel order, alignment, and the treatment of padding.  Retain the original position-table extent.  Validate scale positivity and finiteness, reserved byte values, FP32 parameter finiteness, and every tensor extent.  Specify how initialization records successful validation and preserves that fact while weights remain unchanged, so token calls can reuse it.

Under the proposed layout, the payload calculation is:

| Component | Bytes |
|-----------|------:|
| Twelve blocks' quantized matrices | 84,934,656 |
| Shared quantized embedding and vocabulary matrix | 38,597,376 |
| Retained 907,776 FP32 parameters | 3,631,104 |
| 133,201 FP32 scales | 532,804 |
| Total before format headers and alignment | 127,695,940 |

The exporter must report the final file size and preserve the source checkpoint digest, quantization settings, scale words, tensor offsets, and output digest.  Check exported values and orientation against the Lean quantizer.  A file hash establishes identity.  Relating the exported values to the original FP32 checkpoint requires a checked conversion result or an explicit exporter assumption.  The initial execution theorem can quantify over every model satisfying the new format predicate.

## Implementation and proof milestones

Each milestone records its source revision, proof targets, tested binary hashes, results, and unresolved obligations in the development journal.  Reusable arithmetic, packed-byte, reduction, and ownership results belong in shared support modules.  Reuse unchanged FP32 function proofs through checked instruction-region equality where applicable.

### 1. Approve the design and freeze evaluation inputs

- [x] Approve the algorithm and scalar implementation choices.
- [ ] Select the output-quality criterion for adoption.
- [x] Pin the machine configuration for measurement.  The [evaluation manifest](../data/gpt2-quantized-v1/evaluation.json) fixes the FP32 artifact, source checkpoint, tokenizer, and runtime settings.  The [projection measurements](../data/gpt2-quantized-v1/kernels/wasm-benchmark.json) record the host and CPU configuration.
- [x] Retain the existing 128-prefix sequence and three completion cases.  Fix six held-out prompts and their token IDs for evaluation after the design is frozen.
- [x] List required compiler and binary-checker operations, their existing Talos semantics, and missing proofs.  The [instruction inventory](../proofs/talos/lean/Project/Gpt2QuantizedLinearRows/README.md#arithmetic-and-instructions) records the implemented API and correspondence proofs.

Completion produces an agreed algorithm, file/result formats, instruction inventory, and evaluation manifest.  Dynamic scales still require tests for activation outliers.  [LLM.int8()](https://arxiv.org/abs/2208.07339) gives evidence that outlier handling can affect transformer quantization accuracy.  Measure the pinned GPT-2 checkpoint before deciding whether it needs a different scale rule or mixed-precision exceptions.

### 2. Prove and measure one quantized projection

- [x] Implement the Lean quantizer, signed-byte interpretation, dot product, scale application, and packed output.
- [x] Add the approved compiler operations and efficient byte-array construction.  Prove source/Talos correspondence for rounding and signed numerical conversions.
- [x] Prove integer range, exact accumulation, packed read/write behavior, termination, and store preservation.
- [x] Extend binary syntax, decoding, grammar, validation, translation, and soundness for every emitted new opcode.  Complete an exact-byte package for the projection.
- [x] Test zeros, signed endpoints, half-integer ties, subnormal scales, clipping, rejected values, maximum-length same-sign sums, cancellation, layout boundaries, and allocation reuse.
- [x] Measure the QKV, feed-forward, and vocabulary matrix shapes, including scale computation, quantization, integer products, rescaling, and allocation.  Compare with the existing FP32 projection and a layout-matched FP32 measurement when layout affects the result.

Completion requires a checked kernel artifact and reproducible correctness and timing results.  The measurement determines whether scalar quantization improves speed and which costs dominate.  If it misses the agreed speed criterion, present a measured optimization proposal before full-model integration.  SIMD requires approval and complete instruction and artifact proofs.  A changed binary receives a new artifact identity and verification result.

### 3. Implement and prove cached quantized inference

- [x] Export and validate the quantized checkpoint using the existing Python dependencies.  Retain an independent scalar reference for quantizer and integer-dot tests, and compare FP32 stages in their specified operation order.
- [x] Add quantized embedding lookup and projections, then compose one block, twelve blocks, final normalization, and all vocabulary logits.
- [x] Prove the initialization validator and successful model representation.  Prove the public token step for arbitrary validated weights and represented cache bytes.
- [x] Prove exact status, cache, and logit results for every branch.  Failures after allocation must release temporary buffers and preserve protected inputs.
- [x] Derive allocation sufficiency and address bounds for the full 128-token session, including model validation, quantized activation buffers, FP32 intermediates, returned logits, and cache growth.
- [x] Compose initialization, weight loading, the empty cache, successive calls with fixed weights, reads, and cache/logit releases.  State what happens when an intermediate call returns failure.

Completion requires termination and exact source agreement for the complete session, with a concrete memory bound derived from the new layout and allocation sequence.  The session invariant identifies the prior tokens represented by each cache and preserves validated model bytes.  Host tests cover repeated, changed, and shortened prefixes, reset, the context limit, rejection, and cleanup.  The existing FP32 cache-copy allocation policy supplies the initial comparison point.  A later allocator or cache-layout change requires its own design and proof review.

### 4. Verify and deploy the exact binary

- [x] Register the quantized case and freeze its compiled WASM bytes.  Complete decoding, grammar membership, validation, `CoreValid`, execution-model equality, and transfer of the session theorem.
- [x] Run the focused quantized source and artifact checks, declaration/axiom audit, and independent package check.
- [ ] Complete the required compiler, conformance, and aggregate artifact tests after shared changes.
- [x] Make the quantized host command load the verified frozen artifact and check its hash and model manifest before execution.  Record both identities in every result.
- [x] Run the retained cached-inference and generation tests against those exact bytes.  Preserve the binary, proof package, model manifest, and evaluation records.
- [ ] Complete and retain the cold-checkout reproduction result.

Use the existing repository verification drivers and checked corpus configuration.  Every Lean invocation follows the [development process limits](../DEVELOPING.md#lean-process-limits).  A timeout without a diagnostic requires a smaller proof boundary or a reusable lemma before another attempt.  Review accepted proofs, journals, and telemetry together, including proof effort and shared theorem use.

Binary-profile changes alter the verifier-source identity.  Preserve historical packages and issue updated manifests and certificates where the [artifact format](../docs/artifact-format.md) requires them.  Recheck the FP32 package against the resulting shared verifier.

The remaining proof repairs cover current-source limit and market orders.  Compiler changes altered ownership locals and intermediate-buffer release, so the current proofs require updated free-list invariants.  Historical binary packages retain separate proofs of their original allocation behavior.  The preserved limit, market, and reconstructed-Euler specifications and exact-binary translations now pass.  Aggregate checks and a clean-checkout run follow the remaining repairs.  Quantized inference remains opt-in while output-quality criteria for default adoption remain unresolved.

The theorem specifies calls and byte input/output under Talos semantics.  The runtime uses the pinned Wasmtime configuration, including canonical NaNs.  Tokenization, native host execution, and Wasmtime retain the [existing trust boundary](../training/gpt2/README.md#verification-boundary).  The quantized deployment command must establish which frozen binary it executes.  The current FP32 command recompiles source on invocation, so its build step alone cannot establish that identity.

## Evaluation and adoption

Use the [existing checkpoint and reference harness](../training/gpt2/README.md) for three comparisons: quantized WASM against the specified quantized reference, quantized WASM against FP32 WASM, and both against CPU PyTorch FP32.  Require exact integer and quantizer outputs in the first comparison.  Arithmetic-order differences in a reference must be recorded and resolved before using it as a bitwise oracle.

| Measurement | Required record |
|-------------|-----------------|
| Storage and memory | Weight payload, scales, headers, file size, live tensor bytes, peak WASM linear memory, allocation/free counts, and process peak resident memory.  Attribute cache fragmentation and host-side copies. |
| Runtime | Export, compilation, loading/validation, prompt processing, and generated-token calls measured separately.  Retain repeated warm runs, per-position timing, median and spread, and end-to-end time.  Use the same machine, CPU limits, runtime settings, prompt lengths, and token counts. |
| Logits on fixed prefixes | Compare all 50,257 logits through the existing 128-prefix sequence, plus held-out prompts.  Record maximum absolute and RMS differences, nonfinite results, top-token agreement, winning margins, and per-layer activation/quantization diagnostics. |
| Generated text | Retain greedy token IDs, decoded text, the first differing token, stopping conditions, and completions.  For sampled runs, record the sampler, settings, and random draws.  Compare on a shared fixed prefix separately from each model's generated continuation. |
| Proof coverage | Identify the tested binary and model, theorem assumptions, memory bound, axiom audit, independent verification result, and reproduction commands. |

Keep the FP32 implementation selectable for comparison.  The adoption decision uses measured storage, speed, and output differences against the approved criteria.  Weight payload savings follow from the chosen format.  Speed and peak-memory improvements require execution evidence.  Existing PyTorch/FP32 test tolerances describe that earlier comparison.  Select quantization tolerances through the design review and preserve failures and all evaluated variants.

### Accuracy review after the first candidate

The [first complete-model evaluation](../data/gpt2-quantized-v1/README.md) found
substantial output changes.  All nine completion cases diverge from FP32 within
three generated tokens.  At nine fixed prefixes, the vocabulary projection's
per-row activation scale rounds 79.2–95.6% of coordinates to zero.  The
diagnostic also finds outliers in transformer projections.  The candidate and
approved arithmetic remain the baseline.

The user approved the grouped-activation experiment and prioritized accuracy
investigation over the complete-model proof.  The experiment divides each
activation row into groups of 64 coordinates.  Each group uses the existing
scale and quantizer rules, an integer partial dot product, and FP32 rescaling.
The output sums the rescaled partials in increasing group order from positive
zero, then adds bias once.  Weights retain the current per-output scales.

The experiment compares group size 64 against the current per-row rule
on the fixed prefix trace before evaluating generated text.  A diagnostic
with FP32 vocabulary activations helps separate final-projection error
from earlier error.  Grouped activation scales could preserve more small
coordinates while retaining eight-bit products.  They add FP32 partial-sum
operations and require a revised projection theorem.  The first reference
comparison raises greedy agreement from 87 to 120 of 128 prefixes and reduces
median KL divergence from 0.506706 to 0.009023 nats.  On all 101 prefixes of the
nine prompts, agreement rises from 49 to 85 and median KL falls from 0.677073
to 0.066768.  The FP32 vocabulary-activation control agrees on 87 prefixes.
The nine retained generated texts include readable sampled continuations and
repetitive or incorrect greedy results.  The compiled grouped projection
matches the independent reference byte for byte on four checkpoint shapes
and runs 3.90–4.04 times as fast as FP32.  The compiled grouped model reproduces all reference logits and caches through 128 tokens and all nine completion streams.  Three measured warm traces give a 3.59× median speedup over FP32.  The complete cached-model and session execution proofs pass.  The complete exact-binary package passes independent verification.  Any revised model binary needs a distinct scheme
identifier and proof package.  The nine completion prompts have already been
evaluated and cannot serve as unseen inputs for the revised scheme.

## Subsequent numerical milestone

The user requested completion, commit, and push after reviewing the grouped
experiment.  Completion work uses groups of 64 and resumes the full-model
execution proof.  It includes the numerical obligations in this section.

First prove a local quantization error bound against the exact real value decoded from an FP32 input.  Include scale rounding, the positive scale floor, quotient rounding, nearest-even conversion, clipping, and decoded reconstruction.  A half-scale estimate applies only under the corresponding range and arithmetic assumptions.  Add the clipping term when saturation occurs.

For one linear output, let `x̂` and `ŵ` denote exact scaled quantized values, with component bounds `|x̂_i - x_i| ≤ δx_i` and `|ŵ_i - w_i| ≤ δw_i`.  A reusable real dot-product estimate is:

```text
|sum_i x̂_i ŵ_i - sum_i x_i w_i|
  ≤ sum_i (|w_i| δx_i + |x_i| δw_i + δx_i δw_i).
```

Add integer-to-FP32 conversion, scale-product, output multiplication, and bias-addition errors.  Exact integer accumulation removes accumulation roundoff within the proved range.  Prove the model-export relation needed to instantiate weight errors against the original checkpoint.

Then propagate bounds through quantized embeddings, each block, residual additions, attention, normalization, GELU, and cached key/value history.  State finite-value, magnitude, normalization-denominator, and softmax-denominator assumptions and how they are checked or preserved.  The existing tiny-model results use different widths and arithmetic.  Identify the reusable mathematics and prove the FP32, width-768 instances required here.

The token-choice target compares the quantized and existing FP32 Lean recurrences on the same token prefix.  Prove this relation directly, or bound both computations against a common real algorithm and add both errors.  The existing FP32 execution theorem establishes algorithmic agreement.  A comparison with exact real inference requires an additional FP32 numerical bound.

For finite logits `z` from FP32 inference and `zq` from quantized inference, suppose `|zq_i - z_i| ≤ ε_i`.  If `k` is the FP32 winner and

```text
z_k - z_j > ε_k + ε_j    for every j ≠ k,
```

then `k` is also the quantized winner.  With a uniform bound `ε`, a winning margin greater than `2ε` suffices.  Prove the argmax rule and its tie behavior, then connect it to the returned logit bytes.  A computed certificate uses checked outward bounds for both errors and margins.  Failure to establish the strict inequality returns an inconclusive result.

- [x] Prove scalar quantization and linear-layer error bounds.
- [x] Prove a checked checkpoint-export relation and usable range certificates.
- [x] Compose a stated cached-session logit bound against the selected reference.
- [x] Prove the greedy-margin theorem and produce checked certificates for individual token positions.
- [x] Report certificate coverage and bound sizes on the fixed and held-out inputs.

Identical greedy continuations require induction over the common prefix and successful certification at every generated position, including stopping decisions.  Each accepted step extends that common prefix.  Sampled-token behavior needs a separate numerical statement.
