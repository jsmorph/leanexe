# Pretrained GPT-2 inference source

This directory implements GPT-2 124M inference as pure Lean functions over
packed byte arrays.  LeanExe compiles those functions to WebAssembly.
The model has twelve transformer blocks, width 768, twelve attention heads,
feed-forward width 3,072, and a 50,257-token vocabulary.  It uses binary32
arithmetic and accepts weights as runtime data.

The implementation supports text generation through a cached token step.
Its [execution proofs](../../../proofs/talos/lean/Project/Gpt2CachedStep/README.md)
establish exact agreement with these Lean functions.  The
[GPT guide](../../../docs/gpt/README.md) explains the model families and
verification goals.

## Computation and layout

Token and position embeddings produce a 768-element row.  Each transformer
block applies normalization, query/key/value projection, causal attention,
an output projection and residual addition, then normalization and a
GELU feed-forward network with another residual addition.  Final
normalization and the shared token-embedding matrix produce next-token logits.

All tensor words use little-endian binary32 encoding in `ByteArray` values.
The packed checkpoint contains token embeddings, all 1,024 stored position
rows, twelve blocks, and final normalization parameters.  Its
124,439,808 words occupy 497,759,232 bytes.  The implementation accepts
positions zero through 127.

| Source | Responsibility |
|--------|----------------|
| [Numerical functions](Numerics.lean) | Ordered binary32 exponential approximation, GELU, and comparison operations. |
| [Tensor kernels](Kernel.lean) | Packed word reads, linear projections, normalization, attention, activation, and residual addition. |
| [Transformer block](Block.lean) | Block parameter offsets and composition of tensor kernels. |
| [Full-prefix inference](Inference.lean) | Checkpoint layout, token validation, embeddings, twelve-block traversal, final normalization, and tied vocabulary projection. |
| [Cached inference](Cached.lean) | Attention-cache lookup and extension, one-token block traversal, and the public `cachedStep` entry. |

## Public entries

`infer weights tokens` accepts a packed checkpoint and a nonempty array of
little-endian 32-bit token IDs.  It recomputes a prefix of up to 128 tokens
and returns the final row's 50,257 logits.  An invalid weight length or
token array returns an empty byte array.

`cachedStep weights cache token position` computes one token at the supplied
position.  The incoming cache contains 12 × 1,536 binary32 words per prior
position: keys and values for each layer.  The result contains an extended
cache and all 50,257 logits.  An invalid weight length, token, position, or
cache length returns two empty byte arrays.

The execution theorem quantifies over every weight byte array of the required
size, including exceptional binary32 values.  The
[command-line host](../../../training/gpt2/README.md) uses the pinned pretrained
checkpoint and rejects nonfinite returned logits.  Numerical error bounds
for this model remain deferred.  Tests compare cached and full-prefix
execution, while the complete formal proof specifies the cached recurrence.

## Running and checking

The [checkpoint and runtime instructions](../../../data/gpt2-124m/README.md)
provide setup and measured results.  From the repository root:

```sh
tools/gpt2 --text 'Once upon a time, in a small village' --generate 32
tools/gpt2 --full --text 'Once upon a time, in a small village' --generate 32
tools/talos-proof.js check gpt2_cached_step
```

The CLI compiles the selected entry and starts the Wasmtime host.  The proof
driver regenerates the artifact, compares its execution model with the
tracked proof cache, and checks the registered specification.  These drivers
invoke Lean through the repository's resource-limited runner.
