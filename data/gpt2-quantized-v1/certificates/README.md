# Quantized GPT-2 logit certificates

The [coverage record](coverage.json) contains 229 pairs of logit-array hashes from the frozen FP32 and group64 binaries.  The [Lean checker output](lean-check.log) records every decision.  The checker accepted 119 raw-logit margin certificates and 183 certificates after subtracting a common offset from the quantized logits.

| Input set | Positions | Equal greedy choices | Raw certificates | Common-offset certificates |
|-----------|-----------|----------------------|------------------|----------------------------|
| Retained fixed trace | 128 | 120 | 85 | 116 |
| Nine prompt prefixes | 101 | 85 | 34 | 67 |
| Total | 229 | 205 | 119 | 183 |

These are a posteriori certificates for the supplied logit pairs.  They use the exact observed errors, expressed as integers in units of `2^-149`.  For each competitor `j`, the checker requires the FP32 winning margin to exceed the sum of the winner's and competitor's error bounds.  Equality returns an inconclusive result.  It also checks array lengths, winner membership, and finiteness of every input word.  [The soundness theorem](../../../proofs/talos/lean/Project/ProofKit/F32LogitCertificate.lean) proves that an accepted certificate preserves the unique winner.  [The greedy rule](../../../proofs/talos/lean/Project/ProofKit/GreedyMaximum.lean) retains the first index when logits tie.

The common-offset check subtracts `zq[k] - z[k]` from every quantized logit, using exact integer arithmetic.  This subtraction preserves greedy choices and sets the winner's error to zero.  The largest component error across all pairs is 49.58720397949219 before the subtraction and 8.7122802734375 afterward.  Certificate failure does not establish a changed winner.  Twenty-two agreeing positions remain inconclusive even with the offset.

The capture reproduces all 229 previously recorded group64 logit hashes and all 128 previously recorded FP32 fixed-prefix hashes.  The record identifies both weight files, both binaries, the native host, the capture program, and the Lean checker sources.  Native execution of Wasmtime and the compiled Lean checker remains within the repository's existing runtime trust boundary.

The [packed-word theorem](../../../proofs/talos/lean/Project/ProofKit/PackedLogitCertificate.lean) connects certificates to the returned byte arrays.  The [cached-step theorem](../../../proofs/talos/lean/Project/Gpt2QuantizedCached/LogitCertificates.lean) applies that check to the FP32 and quantized recurrences with their respective caches.  The [session theorem](../../../proofs/talos/lean/Project/Gpt2QuantizedCached/SessionCertificates.lean) proves equal greedy choices throughout a common token sequence when every step passes its certificate.  The captured data above checks supplied output pairs.  It does not evaluate the complete Lean inference recurrence in the kernel.  The [forward numerical theorem](../../../proofs/talos/lean/Project/Gpt2QuantizedCached/Numerical/README.md) now covers the complete cached recurrence under explicit intermediate-range and reconstruction assumptions.  Trace-level checking of every nonlinear assumption and evaluation of that propagated bound remain open.

## Checkpoint export

The [export record](export-check.json) and [checker output](export-check.log) record successful checks of all 123,532,032 coefficients, 133,201 scales, and 907,776 retained FP32 words.  The checker covers the shared embedding/vocabulary matrix and all forty-eight block projections, including their source and target orientations.  Each stored scale equals the specified row scale.  Each coefficient equals the result of FP32 division, clipping, and nearest-even rounding.  Retained FP32 words are finite and unchanged.  The quotient range satisfies the scaled-integer bound with exponent 156.

The [export soundness theorem](../../../proofs/talos/lean/Project/Gpt2QuantizedCached/Export.lean) exposes those conditions for every selected tensor and row.  The [reconstruction theorem](../../../proofs/talos/lean/Project/ProofKit/QuantizedExport.lean) derives the component error, including saturation and division rounding.  The whole-file run uses a native Lean executable compiled from the checked definitions.  Its compiler and runtime remain trusted for data evaluation.  The earlier interpreted run reached its 1,200-second limit before completing the first matrix.

## Activation quantizers

The [activation record](activation-check.json) and [checker output](activation-check.log) cover 233,580 groups and 14,949,120 coefficients across the same 229 prefixes.  Capture reproduces every retained group64 logit hash.  The Lean native checker verifies each group's scale rule, positive finite scale, finite input words, signed coefficients, nearest-even quantization, and quotient range with exponent 156.

The maximum scale is the FP32 word `1074517830`, or 2.185014247894287.  The maximum rounded quotient magnitude is `1123942401`, or `127 + 2^-17`.  The [reconstruction theorem](../../../proofs/talos/lean/Project/ProofKit/QuantizedRangeCertificate.lean) therefore bounds a captured component's local error by its scale times `1/2 + 2^-16`.  The two `2^-17` contributions cover clipping and quotient rounding.  Using the largest scale gives the exact uniform bound `150157618083 / 137438953472`, approximately 1.0925404646186507.  This is an activation reconstruction bound, before multiplication by weights and propagation through later layers.

The capture records contain input words, scale words, and signed coefficients.  Their SHA-256 is `3e578ae5f89bd852a2b778f127418687b640d523352fd3433b4d7e7ac63fba2e`.  Their 75,679,920 bytes remain reproducible under `build`.  Whole-file checking uses the same native Lean compiler/runtime trust boundary as the checkpoint check.

## Normalization ranges

The [normalization record](normalization-check.json) and [compressed arithmetic profiles](normalization-ranges.txt.gz) cover all 11,450 LayerNorm calls across both models and 229 retained prefixes.  Capture reproduces every retained FP32 and group64 logit hash.  The native Lean checker verifies finite inputs and parameters, actual ordered mean and variance sums, every arithmetic-range premise, and a positive denominator lower bound of `1/1000`.  The smallest observed denominator is 0.15138527750968933.

The [checker soundness theorem](../../../proofs/talos/lean/Project/Gpt2QuantizedCached/Numerical/NormalizationRange.lean) supplies the complete normalization premises used by the paired forward bound.  Its real-reference root lower bound holds for every real input because the specified positive epsilon remains in the reference variance.  The [ordered-sum checker](../../../proofs/talos/lean/Project/ProofKit/F32SumRangeCertificate.lean) relates the checked running sums to the source folds.  Candidate exponent selection remains outside the proof.  Each candidate must pass the checked predicate.

## Reproduction

The capture requires the retained model files and native host described in the [evaluation instructions](../README.md).  It writes the raw paired words, a deterministic compressed copy, and their hashes under `build`.  The coverage record preserves those identities.

```sh
training/gpt2/.venv/bin/python training/gpt2/capture_logit_certificates.py
tools/leanrun --timeout 120 lake -d proofs/talos/lean build Project.Gpt2QuantizedCached.CheckLogitCertificates Project.ProofKit.F32LogitCertificateTest
tools/leanrun --timeout 180 lake -d proofs/talos/lean env lean --run proofs/talos/lean/Project/Gpt2QuantizedCached/CheckLogitCertificates.lean build/gpt2-124m/quantized-group64/certificates/logit-pairs.bin
tools/leanrun --timeout 120 lake -d proofs/talos/lean build gpt2-export-check Project.Gpt2QuantizedCached.Export
tools/leanrun --timeout 600 proofs/talos/lean/.lake/build/bin/gpt2-export-check build/gpt2-124m/inference/weights.bin build/gpt2-124m/quantized-group64/weights.bin
training/gpt2/.venv/bin/python training/gpt2/capture_activation_certificates.py
tools/leanrun --timeout 180 lake -d proofs/talos/lean build gpt2-activation-check Project.ProofKit.QuantizedRangeCertificate
tools/leanrun --timeout 600 proofs/talos/lean/.lake/build/bin/gpt2-activation-check build/gpt2-124m/quantized-group64/activations/groups.bin
training/gpt2/.venv/bin/python training/gpt2/capture_normalization_ranges.py
tools/leanrun --timeout 180 lake -d proofs/talos/lean build gpt2-normalization-check Project.Gpt2QuantizedCached.Numerical.NormalizationRange
tools/leanrun --timeout 600 proofs/talos/lean/.lake/build/bin/gpt2-normalization-check build/gpt2-124m/quantized-group64/normalization/rows.bin build/gpt2-124m/quantized-group64/normalization/ranges-ordered.txt
```

The kernel-checked test examples cover a strict accepted margin, a tied maximum, an equality at the error threshold, a changed winner, a common offset, and a nonfinite input.
