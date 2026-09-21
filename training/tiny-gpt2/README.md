# Tiny GPT-2 training

This directory trains small GPT-2-style transformers, exports their
binary64 parameter words, and compares numerical behavior with LeanExe's
WASM implementation.  The models provide a tractable target for inference
and numerical proofs.  The [GPT guide](../../docs/gpt/README.md) explains
the development goals and proof boundaries.

The [architecture](../../plans/tiny-transformer.md) supports four, 64, or 128
byte-token positions, with 2,488, 2,728, or 2,984 parameters.
Each setting has vocabulary 256, one pre-normalized block, two
heads of width two, model width four, feed-forward width eight, tanh GELU,
and a final LayerNorm.  Query, key, and value projections have no biases.
The attention output, both feed-forward projections, and the independent
vocabulary head have biases.  LayerNorm uses epsilon 1/100000.

## Programs and outputs

| Program | Responsibility |
|---------|----------------|
| [PyTorch model](model.py) | Define embeddings, causal attention, feed-forward computation, normalization, and vocabulary projection. |
| [Training](train.py) and [checkpoint support](checkpoint.py) | Train on a byte corpus and preserve tensor shapes, raw parameter words, losses, corpus identity, and training settings. |
| [Model tests](test_model.py) | Check supported dimensions, causal prefixes, finite gradients, and input rejection. |
| [Four-byte fixtures](fixture.py) and [sequence fixtures](sequence_fixture.py) | Export reference tensors consumed by WASM comparison tests. |
| [Attention audit](attention_audit.py) | Search token pairs at active positions for extreme attention-score differences. |
| [Numerical audit](numerical_audit.py) | Reproduce constructed weight cancellation and compare approximation errors against high-precision arithmetic. |

The training program writes a checkpoint.  The inference CLI reads that
checkpoint and passes its parameter words to the generated WASM model.
The [four-byte checkpoint record](../../data/tiny-gpt2-v1/README.md) contains
run commands, retained audits, and the numerical theorems that apply to it.

## Environment and commands

The user approved CPU PyTorch 2.9.1 for training.  The isolated environment
uses Python's standard library and PyTorch.  The requirements file pins the
installed dependency set from the official CPU package index.

```sh
python3 -m venv .venv-tiny-gpt2
.venv-tiny-gpt2/bin/python -m pip install -r training/tiny-gpt2/requirements.txt
.venv-tiny-gpt2/bin/python training/tiny-gpt2/train.py \
  --corpus path/to/corpus.txt --output build/tiny-gpt2/checkpoint.json
.venv-tiny-gpt2/bin/python training/tiny-gpt2/train.py \
  --context 64 --corpus build/tiny-gpt2/tiny-shakespeare.txt \
  --output build/tiny-gpt2/context64-checkpoint.json
.venv-tiny-gpt2/bin/python training/tiny-gpt2/train.py \
  --context 128 --corpus build/tiny-gpt2/tiny-shakespeare.txt \
  --output build/tiny-gpt2/context128-checkpoint.json
.venv-tiny-gpt2/bin/python training/tiny-gpt2/test_model.py
```

Training uses binary64, Adam, one CPU thread, a recorded seed, and a
90/10 contiguous corpus split.  Embeddings start uniform in [-0.02, 0.02].
Projection matrices use Xavier-uniform initialization.  Normalization
scales start at one and biases at zero.  The checkpoint records corpus
identity, training settings, before/after losses, and raw binary64 words.
Matrices use input-by-output row-major order.

## Evidence

All three model sizes pass CPU tests of output shape, causal prefixes,
finite gradients, and input-length rejection.  A nonempty prefix uses the
corresponding first positional rows.
The first [trained checkpoint](../../data/tiny-gpt2-v1/README.md)
uses the approved Tiny Shakespeare corpus and 4,000 Adam steps.
Its validation cross-entropy fell from 5.5688 to 2.7068.
The [64-position checkpoint](../../data/tiny-gpt2-64-v1/README.md) uses
the same corpus and training settings.  Its validation cross-entropy fell
from 5.5676 to 2.6964.
The [128-position checkpoint](../../data/tiny-gpt2-128-v1/README.md) has
validation cross-entropy 2.6916 after the same number of training steps.
The four-byte CLI now has checkpoint-independent checking, exact execution,
and numerical-error theorems.  Complete execution proof work for the longer
tiny model is paused.  [Pretrained GPT-2 124M](../../data/gpt2-124m/README.md)
has separate cached-step, session, and exact-binary execution proofs.
The sampled intermediate ranges in an exported checkpoint are measurements.
The source-equivalence proof takes the Lean computation as its specification.

The [runtime-weight analysis](../../plans/tiny-model-runtime-weights.md)
records the clipping proposal and numerical sensitivity investigation.
Its standard-library audit reproduces the constructed cancellation case
against the current WASM artifact and evaluates proposed exp/GELU arithmetic:

```sh
python3 training/tiny-gpt2/numerical_audit.py \
  --output data/tiny-gpt2-v1/numerical-audit.json
```

The output records raw test weights, the module hash, an 80-digit reference,
sampled approximation errors, and conservative sensitivity terms at context
lengths four and sixty-four.  These calculations guide the formal proof.

`node test/tiny_gpt2_body.js` compares sixteen initialized model rows with
the compiled hidden-state and vocabulary-head bodies.  Wasmtime agrees
bit-for-bit with the native Talos evaluator.  The
[model layout record](../../plans/tiny-model-layout.md) gives the measured
PyTorch differences and proof status.

The training and export code uses tensor operations and standard-library
binary packing.  The pretrained model uses a separate
[uv project](../gpt2/pyproject.toml) with the approved PyTorch, NumPy, and
Transformers dependencies.

The [pinned TorchLean architecture](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/API/Models/CausalTransformer/Architecture.lean)
and [attention implementation](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/Runtime/Autograd/Model/Layers/Attention.lean)
define the audited dimensions, biases, head layout, and scaling.
