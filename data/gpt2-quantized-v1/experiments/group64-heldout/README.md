# Group64 held-out evaluation

The [six input prompts](../../heldout-group64.json) were frozen in commit `739f4f4f` before evaluation.  They were selected after the group64 implementation and were not used to tune its arithmetic.  The [completion record](completions.json) retains all token IDs, texts, stopping conditions, memory observations, and binary identities.  The first differing generated token occurs at positions 7, 3, 4, 11, 6, and 1 for narrative, exposition, dialogue, code, numeric prose, and technical explanation respectively.  Both models produce repetitive or incorrect continuations in this sample.

The [paired-logit record](coverage.json) covers all 73 shared prompt prefixes and all 50,257 logits per prefix.  Greedy winners agree at 58 positions.  The largest raw-logit difference is 18.120101928710938.  The largest per-vector RMS difference is 13.911928369136579.  All outputs are finite.

The [Lean checker output](lean-check.log) accepts 26 raw-logit and 49 common-offset greedy-margin certificates.  Nine agreeing positions remain inconclusive after subtracting the winning logit's common offset.  Each Lean result agrees with the integer precheck.  These certificates use observed logit differences.  They do not evaluate the propagated forward bound or certify complete generated continuations.

The deployed module has SHA-256 `9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075`.  The FP32 module has SHA-256 `e93de126e00d7f5c5b9b30ca014a13b1385e9f91e3cb6b4e56a4aacf7a2b4ade`.  These exploratory execution times were measured during proof work and are not controlled benchmark results.  The earlier repeated warm benchmark supplies the performance comparison.

## Reproduction

```sh
training/gpt2/.venv/bin/python training/gpt2/compare_quantized_text.py --grouped --evaluation data/gpt2-quantized-v1/heldout-group64.json --wasm proofs/artifacts/gpt2_quantized_cached/9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075/program.wasm --output build/gpt2-124m/quantized-group64/heldout/completions.json
training/gpt2/.venv/bin/python training/gpt2/capture_logit_certificates.py --evaluation data/gpt2-quantized-v1/heldout-group64.json --output build/gpt2-124m/quantized-group64/heldout/certificates
tools/leanrun --timeout 180 lake -d proofs/talos/lean env lean --run proofs/talos/lean/Project/Gpt2QuantizedCached/CheckLogitCertificates.lean build/gpt2-124m/quantized-group64/heldout/certificates/logit-pairs.bin
```
