# Tiny GPT-2 checkpoint

This checkpoint contains 2,488 binary64 parameters for the
[agreed architecture](../../plans/tiny-transformer.md).  The user approved
Tiny Shakespeare and a command-line interface returning all 256 next-byte
logits on 2026-09-16.  The complete generated-WAT execution proof passes.
Checkpoint certificates establish finite outputs for every four-byte input.
The composed numerical error bound remains in progress.

## Command-line inference

```sh
tools/tiny-gpt2.js --text 'To b'
tools/tiny-gpt2.js --tokens 0 0 36 82
```

Each command accepts four bytes and returns all 256 next-byte logits in one
WASM call.  JSON output contains decimal logits, raw binary64 words, input
tokens, artifact hashes, and the current verification status.  The host
checks the recorded checkpoint and module hashes before execution.
The 17,371-byte [module](inference.wasm) runs through the existing Wasmtime
C host.  The separate 16,006-byte hidden-state module has a
[proof](../../proofs/talos/lean/Project/TinyGpt2Hidden/Hidden.lean) of termination,
exact agreement with the raw-bit model, and store preservation for every
four-byte input.  The
[complete inference theorem](../../proofs/talos/lean/Project/TinyGpt2Infer/Inference.lean)
proves termination, all 256 raw-bit logits, checkpoint preservation, and a
fixed page count.  It assumes a represented weight array of at least 2,488
words, an empty initial free list, weights below the output heap, and enough
reserved memory.  Output construction requires 277,560 bytes.  With the CLI's
weight array allocated first, its final heap top is 301,616, within the
module's sixteen initial pages.  The composed numerical certificate remains
open.  The host and exact-byte package remain outside this execution theorem.

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
logits of magnitude at most 117 for every four-byte input.  The composed
error bound against the real model remains open.

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
from 383.216 with the previous arithmetic.  This measurement does not
establish the pending uniform logit error bound.

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
```

The [inference source](../../proofs/talos/lean/Project/TinyGpt2/Inference.lean)
computes the final hidden row and appends one logit per vocabulary token.
To reproduce the compiled module:

```sh
tools/leanrun --timeout 3m lake -d proofs/talos/lean build Project.TinyGpt2.Inference
tools/leanrun --timeout 3m lake -d proofs/talos/lean env \
  .lake/build/bin/lean-wasm compile --module Project.TinyGpt2.Inference \
  --entry Project.TinyGpt2.infer --out build/tiny-gpt2/inference.wasm
```
