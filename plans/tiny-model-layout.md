# Tiny model weight layout

The [arithmetic body](../proofs/talos/lean/Project/TinyGpt2/Model.lean)
reads 2,488 binary64 words from a runtime array.  Matrices use input-by-output
row-major order.  The [real decoding](../proofs/talos/lean/Project/TinyGpt2/Decoding.lean)
interprets each stored word as its exact real value and constructs the
parameters of the [real model](../proofs/talos/lean/Project/TinyGpt2/Real.lean).

## Tensor offsets

Offsets count words from the start of the array payload.

| Tensor | Shape | Offset |
|--------|-------|--------|
| Token embeddings | 256 × 4 | 0 |
| Position embeddings | 4 × 4 | 1024 |
| Query | 4 × 4 | 1040 |
| Key | 4 × 4 | 1056 |
| Value | 4 × 4 | 1072 |
| Attention output | 4 × 4 | 1088 |
| Attention bias | 4 | 1104 |
| Feed-forward expansion | 4 × 8 | 1108 |
| Expansion bias | 8 | 1140 |
| Feed-forward contraction | 8 × 4 | 1148 |
| Contraction bias | 4 | 1180 |
| Vocabulary head | 4 × 256 | 1184 |
| Vocabulary bias | 256 | 2208 |
| First normalization scale and bias | 4 + 4 | 2464 |
| Second normalization scale and bias | 4 + 4 | 2472 |
| Final normalization scale and bias | 4 + 4 | 2480 |

## Arithmetic and evidence

The shared row operations use balanced dot products, the existing
LayerNorm calculation, exponential softmax, and the GELU evaluator with
proved tail bounds.  Each head divides its two-coordinate dot product by
binary64 word 3ff6a09e667f3bcd, the rounded square root of two.  Its local
score theorem includes constant and division errors.

The initial hidden-state body compiled to a 15,423-byte WASM module.  The deterministic
initialization test covers four contexts at all four output positions.
Wasmtime and the native Talos evaluator agree on every hidden-state word
and four selected vocabulary logits per position.  The test also checks
causal-prefix equality and that hidden-state execution allocates only the
host-supplied weight array.

```sh
node test/tiny_gpt2_body.js
```

This test requires the approved [training environment](../training/tiny-gpt2/README.md).
The fixture contains initialization weights and records that no training
occurred.  Its maximum measured PyTorch differences are approximately
3.86 × 10^-6 for hidden coordinates and 5.49 × 10^-7 for selected logits.
Those comparisons supply empirical evidence.  The
[hidden-state execution theorem](../proofs/talos/lean/Project/TinyGpt2Hidden/Hidden.lean)
now proves termination, exact raw-bit model agreement, and store preservation
for all four-byte inputs and represented weight arrays of at least 2,488 words.
The complete inference module reuses this composition proof for its internal
hidden function, and its single-logit function has a checked execution theorem.
The [complete inference execution proof](../proofs/talos/lean/Project/TinyGpt2Infer/Inference.lean)
now includes the vocabulary loop, allocation, and release.  It proves exact
output, checkpoint preservation, and a fixed page count under its memory
assumptions.  Checkpoint range certificates establish finite hidden
coordinates and logits for every four-byte input.  The composed numerical
logit bound is proved, parameterized by the weight cap and normalization
lower bounds.  Its unconditional estimate is too coarse to certify precision.
The checked CLI accepts runtime weights and rejects or clips them through
the proved entry.
