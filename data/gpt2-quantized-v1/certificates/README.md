# Quantized GPT-2 logit certificates

The [coverage record](coverage.json) contains 229 pairs of logit-array hashes from the frozen FP32 and group64 binaries.  The [Lean checker output](lean-check.log) records every decision.  The checker accepted 119 raw-logit margin certificates and 183 certificates after subtracting a common offset from the quantized logits.

| Input set | Positions | Equal greedy choices | Raw certificates | Common-offset certificates |
|-----------|-----------|----------------------|------------------|----------------------------|
| Retained fixed trace | 128 | 120 | 85 | 116 |
| Nine prompt prefixes | 101 | 85 | 34 | 67 |
| Total | 229 | 205 | 119 | 183 |

These are a posteriori certificates for the supplied logit pairs.  They use the exact observed errors, expressed as integers in units of `2^-149`.  For each competitor `j`, the checker requires the FP32 winning margin to exceed the sum of the winner's and competitor's error bounds.  Equality returns an inconclusive result.  It also checks array lengths, winner membership, and finiteness of every input word.  [The soundness theorem](../../../proofs/talos/lean/Project/ProofKit/F32LogitCertificate.lean) proves that an accepted certificate preserves the unique winner.  [The greedy rule](../../../proofs/talos/lean/Project/ProofKit/GreedyMaximum.lean) retains the first index when logits tie.

The common-offset check subtracts `zq[k] - z[k]` from every quantized logit, using exact integer arithmetic.  This subtraction preserves greedy choices and sets the winner's error to zero.  The largest component error across all pairs is 49.58720397949219 before the subtraction and 8.7122802734375 afterward.  Certificate failure does not establish a changed winner.  Twenty-two agreeing positions remain inconclusive even with the offset.

The capture reproduces all 229 previously recorded group64 logit hashes and all 128 previously recorded FP32 fixed-prefix hashes.  The record identifies both weight files, both binaries, the native host, the capture program, and the Lean checker sources.  Native execution of Wasmtime and the compiled Lean checker remains within the repository's existing runtime trust boundary.  The checked margin theorem concerns supplied words.  Connecting numerical certificates to the formal cached recurrences and deriving forward bounds through every transformer operation remain open.

## Reproduction

The capture requires the retained model files and native host described in the [evaluation instructions](../README.md).  It writes the raw paired words, a deterministic compressed copy, and their hashes under `build`.  The coverage record preserves those identities.

```sh
training/gpt2/.venv/bin/python training/gpt2/capture_logit_certificates.py
tools/leanrun --timeout 120 lake -d proofs/talos/lean build Project.Gpt2QuantizedCached.CheckLogitCertificates Project.ProofKit.F32LogitCertificateTest
tools/leanrun --timeout 180 lake -d proofs/talos/lean env lean --run proofs/talos/lean/Project/Gpt2QuantizedCached/CheckLogitCertificates.lean build/gpt2-124m/quantized-group64/certificates/logit-pairs.bin
```

The kernel-checked test examples cover a strict accepted margin, a tied maximum, an equality at the error threshold, a changed winner, a common offset, and a nonfinite input.
