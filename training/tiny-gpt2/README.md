# Tiny GPT-2 training

This directory trains the architecture in the
[inference plan](../../plans/tiny-transformer.md).  It has 2,488 parameters:
four byte-token positions, vocabulary 256, one pre-normalized block, two
heads of width two, model width four, feed-forward width eight, tanh GELU,
and a final LayerNorm.  Query, key, and value projections have no biases.
The attention output, both feed-forward projections, and the independent
vocabulary head have biases.  LayerNorm uses epsilon 1/100000.

## Environment and commands

The user approved CPU PyTorch 2.9.1 for training.  The isolated environment
uses Python's standard library and PyTorch.  The requirements file pins the
installed dependency set from the official CPU package index.

```sh
python3 -m venv .venv-tiny-gpt2
.venv-tiny-gpt2/bin/python -m pip install -r training/tiny-gpt2/requirements.txt
.venv-tiny-gpt2/bin/python training/tiny-gpt2/train.py \
  --corpus path/to/corpus.txt --output build/tiny-gpt2/checkpoint.json
```

Training uses binary64, Adam, one CPU thread, a recorded seed, and a
90/10 contiguous corpus split.  Embeddings start uniform in [-0.02, 0.02].
Projection matrices use Xavier-uniform initialization.  Normalization
scales start at one and biases at zero.  The checkpoint records corpus
identity, training settings, before/after losses, and raw binary64 words.
Matrices use input-by-output row-major order.

## Evidence

The model's shape, causal prefix equality, and finite gradients pass a
direct CPU test.  The first [trained checkpoint](../../data/tiny-gpt2-v1/README.md)
uses the approved Tiny Shakespeare corpus and 4,000 Adam steps.
Its validation cross-entropy fell from 5.5688 to 2.7068.
Exported-weight verification remains open.
The sampled intermediate ranges in an exported checkpoint are measurements.
The inference proof must establish its own ranges and error bounds.

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

PyTorch reports that optional NumPy integration is unavailable in this
environment.  The training and export code uses tensor operations and
standard-library binary packing.

The [pinned TorchLean architecture](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/API/Models/CausalTransformer/Architecture.lean)
and [attention implementation](https://github.com/lean-dojo/TorchLean/blob/4ec1f62bf8308e2dc7f4d73e64205e66270ccfd1/NN/Runtime/Autograd/Model/Layers/Attention.lean)
define the audited dimensions, biases, head layout, and scaling.
