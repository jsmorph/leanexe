# GPT inference and verification

[LeanExe's](../../README.md) GPT work implements transformer inference in Lean,
compiles it to WebAssembly, and proves properties of the resulting programs.  A model takes
stored parameters and token IDs and returns a logit, or unnormalized score,
for each possible next token.  A host program selects a token and repeats
inference to generate text.

The work has two goals: prove that executable inference agrees with its Lean
algorithm, including memory use and termination, and bound numerical error
against real arithmetic.  Small trained models support the numerical work.
Pretrained GPT-2 supplies a larger execution and artifact-verification case.

## Models and results

| Model | Input and representation | Current result |
|-------|--------------------------|----------------|
| [Four-byte tiny GPT-2](../../data/tiny-gpt2-v1/README.md) | Four byte tokens, 2,488 binary64 parameters, one width-four transformer block, 256 output logits. | Complete generated-WAT execution and numerical proofs, with runtime weight validation and clipping.  The unconditional error bound is too coarse to certify precision. |
| [64-position](../../data/tiny-gpt2-64-v1/README.md) and [128-position tiny GPT-2](../../data/tiny-gpt2-128-v1/README.md) | Byte tokens, the same block dimensions, and longer position tables. | Trained checkpoints and CPU tests.  The 128-position model also generates text in WASM.  Its complete execution proof remains open. |
| [Pretrained GPT-2 124M](../../data/gpt2-124m/README.md) | Up to 128 byte-pair tokens, 124,439,808 binary32 parameters, twelve width-768 blocks, 50,257 output logits. | Cached WASM generation, exact token-step and session proofs, and a proof about the distributed binary.  Real-arithmetic error bounds remain deferred. |

The pretrained checkpoint retains its original 1,024 positional embeddings.
The implementation and session theorem support positions zero through 127.

## Data and execution

The tiny-model training program writes a checkpoint containing named tensors
and raw binary64 parameter words.  Its CLI passes the weights, four byte
tokens, and a weight bound to a checked WASM entry.  The entry validates the
inputs, clips finite weights to the requested interval, runs the transformer,
and returns all 256 logits.  The [training directory](../../training/tiny-gpt2/README.md)
contains the PyTorch model, exporter, and numerical audits.  The
[tiny-model source](../../proofs/talos/lean/Project/TinyGpt2/README.md)
defines the inference algorithm and real-arithmetic comparison.

For pretrained GPT-2, the [Python programs](../../training/gpt2/README.md)
download and check a pinned checkpoint, export packed binary32 weights,
and tokenize text.  LeanExe compiles the [Lean model](../../LeanExe/Models/Gpt2/README.md)
to WASM.  The C host loads that module and the weights into a resident
Wasmtime instance.  Each call consumes the next token and an attention
key/value cache, then returns an updated cache and 50,257 logits.  Python
reads the logits, releases the old buffers, selects the next token, and
decodes the generated token sequence as text.

Commands run from the repository root after the setup in the linked model
documents and [development guide](../../DEVELOPING.md):

```sh
tools/tiny-gpt2.js --text 'To b'
tools/tiny-gpt2.js --context 128 --text 'ROMEO:' --generate 160
tools/gpt2 --text 'Once upon a time, in a small village' --generate 32
```

The 128-position tiny model advances a window of byte tokens.  Pretrained
GPT-2 stops at 128 total tokens, including the prompt.

## Proofs and evidence

| Question | Evidence and scope |
|----------|--------------------|
| Does generated WASM compute the Lean algorithm? | [Tiny checked-entry proofs](../../proofs/talos/lean/Project/TinyGpt2Checked/README.md) and [pretrained cached-inference proofs](../../proofs/talos/lean/Project/Gpt2CachedStep/README.md) establish exact results, termination, and stated memory properties in Talos's WASM semantics. |
| Does the distributed pretrained binary have that behavior? | The cached-inference artifact proof checks its embedded bytes, decoding, validation, and equality with the execution model, then applies the session theorem. |
| How close are computed logits to real arithmetic? | Tiny-model numerical theorems bound outputs and error for a specified weight domain and normalization bounds.  The checked entry compares against the real model using clipped weights.  Fixed-checkpoint certificates cover every four-byte input. |
| How does inference compare with PyTorch? | Checkpoint records retain measured logits, intermediate tensors, completions, and memory use.  The tiny-model audits also retain adversarial token and weight cases that exposed unsuitable numerical domains and approximation error. |

Execution equality fixes the implemented arithmetic, including its
approximations and exceptional floating-point values.  Numerical theorems
add real-arithmetic claims under their stated assumptions.  Tokenization,
sampling, the native host, and Wasmtime are outside the Lean proof.

The [Talos proof inventory](../../proofs/talos/README.md) records registered
theorems and check commands.  The [GPT execution report](../../paper/gpt2-comprehensive-report/README.md)
covers the CPU implementation and the separate WGSL branch's shader and
browser work.  The [numerical-bounds draft](https://github.com/jsmorph/cap/blob/a6a48a4/reports/gpt-bounds-2026-09-21/README.md)
examines the tiny model's bounds and adversarial cases.  That draft remains
unsubmitted.
