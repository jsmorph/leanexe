# Quantized GPT-2 source

This candidate evaluates the pretrained GPT-2 124M model with signed eight-bit
learned weights and projection inputs, signed 32-bit accumulation, and FP32
rescaling.  The cached candidate uses independent activation scales for
consecutive groups of 64 coordinates.  Attention, cache values, normalization, GELU, and softmax retain
the existing FP32 operations.  The [approved design](../../../../plans/gpt2-quantized.md)
specifies rounding and saturation.  The [model format](../../../../plans/gpt2-quantized-format.md)
defines tensor extents, validation, and status values.

## Definitions

| Module | Responsibility |
|--------|----------------|
| [Projection kernel](Kernel.lean) | Per-row activation scales, nearest-even quantization, signed dot products, FP32 reconstruction, and checked projection. |
| [Grouped projection](Grouped.lean) | Activation groups of 64 with FP32 addition of rescaled partial sums. |
| [Model format](Format.lean) | Header, tensor offsets, coefficient and scale checks, and complete initialization validation. |
| [Cached inference](Cached.lean) | Shared embedding lookup, twelve transformer blocks, cache updates, final normalization, vocabulary projection, and failure results. |

The grouped projection requires an input width divisible by 64,
finite FP32 inputs, valid coefficient and scale values, and sufficient buffers.
The cached model uses widths 768 and 3072.  It starts the FP32 sum at positive
zero, processes groups in increasing order, and adds bias once.  Scheme 2 in
the model header distinguishes this arithmetic from the retained per-row
scheme.  Every integer prefix within a group has magnitude at most 1,032,256.

`validateModel` and `cachedStep` share one WASM instance and loaded weight
buffer.  The [host prototype](../../../../training/gpt2/quantized_wasm.py)
validates the model once and preserves its bytes across calls.  Each step
checks the header, token, position, cache shape, and cache finiteness.
Numerical failures return status four and empty output buffers.  The caller
retains its preceding cache until a successful call returns the replacement.

## Evidence

The [scalar projection proof](../../../../proofs/talos/lean/Project/Gpt2QuantizedLinearRows/README.md)
covers exact execution, integer range, allocation, release, and its frozen
binary.  The [cached proof work](../../../../proofs/talos/lean/Project/Gpt2QuantizedCached/README.md)
has checked helper-region equality.  Complete-model execution, session memory
bounds, and exact-binary proofs remain open.

The [evaluation records](../../../../data/gpt2-quantized-v1/README.md) retain
bitwise reference tests, memory measurements, timing, generated texts, and
activation-error diagnostics.  The original per-row candidate reduces storage
and measured runtime, but its completion quality deteriorates under that scale rule.
The grouped reference improves agreement with FP32 on both evaluated prefix
sets.  Its experimental projection binary passes bitwise reference tests and
timing comparisons.  The grouped cached WASM matches all reference logits and caches through 128 tokens.  The grouped projection execution proof passes.  Complete cached-model and exact-binary proofs remain open.
