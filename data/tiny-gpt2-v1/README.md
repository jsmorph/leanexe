# Four-byte GPT-2 checkpoint and inference

This directory contains a trained GPT-2-style model, its WASM inference
modules, and numerical evidence.  The model takes four byte tokens and
returns 256 next-byte logits.  Its 2,488 binary64 parameters define one
width-four transformer block with two attention heads and a width-eight
feed-forward layer.  Training uses Tiny Shakespeare.

The [GPT guide](../../docs/gpt/README.md) explains the development goals and
related models.  The [model and numerical proofs](../../proofs/talos/lean/Project/TinyGpt2/README.md)
define the computation and its real-arithmetic comparison.  The complete
generated-WAT execution proof passes.
Checkpoint certificates establish finite outputs for every four-byte input.
The composed numerical theorem is proved.  Its unconditional error estimate
is too coarse to certify precision.  The CLI uses the proved runtime
weight checker and accepts replacement checkpoints without new proofs.

## Command-line inference

```sh
tools/tiny-gpt2.js --text 'To b'
tools/tiny-gpt2.js --tokens 0 0 36 82
tools/tiny-gpt2.js --checkpoint data/tiny-gpt2-v1/checkpoint.json --bound 3 --text 'To b'
```

Each command accepts four bytes and returns all 256 next-byte logits in one
WASM call.  The bound defaults to 10.  The entry rejects nonfinite weights,
invalid weight counts, and bounds outside [0, 10].  It clips finite weights
to [-B, B].  Both signed-zero bounds are accepted.  Numerical guarantees
refer to the real model using the clipped weights.

JSON output contains `accepted`, decimal logits, raw binary64 words, input
tokens, the bound and its exact word, artifact hashes, and verification
status.  Rejection returns `accepted: false` and empty logit arrays.  The
CLI checks checkpoint syntax and the 2,488-word count before the WASM call.
Custom files use the same named tensor `bits` arrays as the
[checkpoint](checkpoint.json).  Replacing their values requires no new
inference proof.  The CLI checks the published module hash and the default
checkpoint hash, and reports the hash of every supplied checkpoint.

The 19,397-byte [checked module](checked-inference.wasm) runs through the
existing Wasmtime C host.  Its
[execution theorem](../../proofs/talos/lean/Project/TinyGpt2Checked/Entry.lean)
proves termination, exact output, input preservation, and a fixed page
count for both acceptance and rejection.  It assumes represented input,
an empty initial free list, input below the allocation top, and enough
reserved memory.  For n supplied words, the conservative reservation is
48+8(n+1)+277,560 bytes.  The CLI's 2,488-word input gives a final heap top
of 321,576, within the module's sixteen initial pages.  Temporary clipped
weights remain in the arena until its reset.

The [numerical execution theorem](../../proofs/talos/lean/Project/TinyGpt2Checked/Numerical.lean)
adds finite logits of magnitude at most 1,260 and the composed error bound
for every accepted weight array and four-byte context.  It retains B and
three normalization lower bounds as parameters.  The host and exact-byte
package remain outside this theorem.  The earlier 17,371-byte
[raw inference module](inference.wasm) remains available for arithmetic
comparisons, with its [execution proof](../../proofs/talos/lean/Project/TinyGpt2Infer/Inference.lean).

## Training record

The corpus is [Tiny Shakespeare from char-rnn](https://github.com/karpathy/char-rnn/blob/6f9487a6fe5b420b7ca9afb0d7c078e37c1d1b4e/data/tinyshakespeare/input.txt),
at revision `6f9487a6fe5b420b7ca9afb0d7c078e37c1d1b4e`.
Its 1,115,394 bytes have SHA-256
`86c4e6aa9db7c042ec79f339dcb96d42b0075e16b8fc2e86bf0ca57e2dc565ed`.
Training uses the first 1,003,854 bytes.  Validation uses the remaining
111,540 bytes, with five-byte windows confined to each split.

CPU PyTorch 2.9.1 trained the model in binary64 for 4,000 Adam steps with
seed 17, batch size 128, and learning rate 0.001.  Each loss estimate uses
8,192 windows selected at uniform index intervals in its split.

| Cross-entropy, natural logarithms | Initialization | Trained |
|---------------------------------|----------------|---------|
| Training | 5.571608828427468 | 2.694080450661182 |
| Validation | 5.568786144189691 | 2.7068412114331264 |

The [checkpoint](checkpoint.json) records raw weight words, tensor shapes,
training settings, loss estimates, and sampled ranges.  Those ranges guide
the proof investigation.  The proof must cover every accepted byte context.

The [attention audit](attention-audit.json) enumerates all token pairs at
distinct active key positions in CPU binary64 arithmetic.  It retains a
context attaining each reported maximum.  Bytes `[0, 0, 36, 82]` give a
spread of 12.117768731550278 in the second head at the final position.
The wider softmax theorem covers every finite row whose active score
differences are below 2^1023.  The
checkpoint's [range proof](../../plans/tiny-model-range-analysis.md)
now establishes real score spread at most 103/7 for every accepted context.
The binary64 certificate adds normalization, projection, and score errors
and proves computed spread at most sixteen.  Every byte embedding satisfies
the first normalization domain.  Lean also proves that all 2,488 weights
are finite with real magnitude at most four.  The real first residual has
component magnitude at most 18/5, and the computed residual is bounded by
37/10.  The feed-forward and final-normalization domains are proved.
The [output certificate](../../proofs/talos/lean/Project/TinyGpt2/CheckpointLogits.lean)
proves finite hidden coordinates of magnitude at most seven and finite
logits of magnitude at most 117 for every four-byte input.

The compiled body passes 24 context-position tests, including that witness.
Every hidden-state word and 96 selected logits match the native Talos bit
model.  Maximum empirical differences from CPU PyTorch are approximately
5.996 × 10^-15 for hidden coordinates and 1.155 × 10^-14 for selected logits.
The complete inference entry also matches all 1,536 output words from six
contexts against the native Talos bit model.  Its largest measured
CPU PyTorch difference is 7.994 × 10^-15.

The artifact uses the verified degree-eighteen negative exponential and
wider GELU.  The [cancellation audit](numerical-audit.json) now measures
absolute logit error 9.325 × 10^-11 against its 80-digit reference, down
from 383.216 with the previous arithmetic.

The [composed source theorem](../../proofs/talos/lean/Project/TinyGpt2/NumericalLogits.lean)
compares all 256 logits with the existing real model.  It accepts weight
cap B in [0, 10] and positive lower bounds for the three normalization
stages, covering both decoded computed inputs and real inputs.  The square
root of the epsilon floor always qualifies.  With B = 10 and those floors,
the composed error formula evaluates to approximately 2.934 × 10^14.
The [checked execution theorem](../../proofs/talos/lean/Project/TinyGpt2Checked/Numerical.lean)
takes the minimum of that formula and the magnitude bound
1,260 + 12B² + B.  At B = 10, this proves absolute error at most 2,470
for each logit.  This bound is too coarse to certify precision.  Larger
certified normalization lower bounds can sharpen the composed formula.
These theorems require no checkpoint facts and compare against real
arithmetic using the clipped weights.

## Reproduction

The generated Lean weight array and its numerical certificates can be checked
against this checkpoint with:

```sh
tools/tiny-gpt2-certificate.js --check
tools/leanrun --timeout 3m lake -d proofs/talos/lean build \
  Project.TinyGpt2.CheckpointLogits
```

The [training environment](../../training/tiny-gpt2/README.md) records the
approved dependencies.  From the repository root:

```sh
curl --fail --silent --show-error --output build/tiny-gpt2/tiny-shakespeare.txt \
  https://raw.githubusercontent.com/karpathy/char-rnn/6f9487a6fe5b420b7ca9afb0d7c078e37c1d1b4e/data/tinyshakespeare/input.txt
sha256sum build/tiny-gpt2/tiny-shakespeare.txt
.venv-tiny-gpt2/bin/python training/tiny-gpt2/train.py \
  --corpus build/tiny-gpt2/tiny-shakespeare.txt \
  --output build/tiny-gpt2/checkpoint.json
.venv-tiny-gpt2/bin/python training/tiny-gpt2/attention_audit.py \
  --checkpoint data/tiny-gpt2-v1/checkpoint.json \
  --output build/tiny-gpt2/attention-audit.json
node test/tiny_gpt2_body.js --checkpoint data/tiny-gpt2-v1/checkpoint.json
node test/tiny_gpt2_checked.js
```

The [inference source](../../proofs/talos/lean/Project/TinyGpt2/Inference.lean)
computes the final hidden row and appends one logit per vocabulary token.
The checked wrapper validates and clips weights before calling that body.
To reproduce the CLI module:

```sh
tools/leanrun --timeout 3m lake -d proofs/talos/lean build Project.TinyGpt2.Checked
tools/leanrun --timeout 3m lake -d proofs/talos/lean env \
  .lake/build/bin/lean-wasm compile --module Project.TinyGpt2.Checked \
  --entry Project.TinyGpt2.inferChecked --out build/tiny-gpt2/checked-inference.wasm
```
