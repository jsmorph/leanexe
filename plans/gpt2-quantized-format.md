# Quantized GPT-2 file and session API

The user approved this file and public API on 2026-09-22.  It completes the interface choices in the [implementation plan](gpt2-quantized.md).

After the grouped experiment, the user requested completion, commit, and push.
The grouped candidate uses scheme 2.  Scheme 1 identifies the retained per-row
candidate.  Both schemes use the same tensor payload and session API.

## File format

Version 1 stores the approved GPT-2 124M architecture in 127,695,972 bytes: a 32-byte header and a 127,695,940-byte payload.  All words use little-endian encoding.  Every tensor begins at a multiple of four bytes.  The format has fixed offsets and no padding.

| Byte offset | Field | Required value |
|------------:|-------|----------------|
| 0 | Eight magic bytes | ASCII `LXQGPT2` followed by zero. |
| 8 | Format version, `UInt32` | 1. |
| 12 | Header length, `UInt32` | 32. |
| 16 | Payload length, `UInt32` | 127,695,940. |
| 20 | Quantization scheme, `UInt32` | 2: activation groups of 64, symmetric nearest-even quantization, and FP32 addition of rescaled group sums. |
| 24 | Maximum inference context, `UInt32` | 128. |
| 28 | Reserved word, `UInt32` | Zero. |

The payload begins with the shared token coefficients, token scales, and all 1,024 FP32 position rows.  Twelve equal-sized transformer blocks follow.  Each block stores its first normalization scale and bias, QKV coefficients/scales/bias, attention-output coefficients/scales/bias, second normalization scale and bias, expansion coefficients/scales/bias, and reduction coefficients/scales/bias.  Final normalization scale and bias end the file.

| Region | Absolute byte offset | Byte length |
|--------|---------------------:|------------:|
| Shared token coefficients | 32 | 38,597,376 |
| Token scales | 38,597,408 | 201,028 |
| Position embeddings | 38,798,436 | 3,145,728 |
| Transformer blocks | 41,944,164 | 12 × 7,145,472 |
| Final normalization scale | 127,689,828 | 3,072 |
| Final normalization bias | 127,692,900 | 3,072 |

Matrices store output channels as contiguous rows.  Each row has one positive finite normal FP32 scale and signed coefficients in `[-127,127]`.  The validator rejects byte `0x80`, nonfinite retained FP32 parameters, invalid scales, every incorrect header field, and any file-length mismatch.  The exporter writes a JSON manifest containing the original checkpoint hash, quantization settings, tensor extents, model hash, and file size.  The host checks both model and binary identities when opening a session.

## Session API

`validateModel weights` returns a status word.  The host calls it once after loading the model, records success, and keeps the model buffer unchanged until session close.  The token-step theorem assumes the validated model predicate.  A session proof connects that premise to successful validation and preservation of the model bytes.

`cachedStep weights cache token position` returns a status, a cache byte array, and a logit byte array.  Success returns the existing FP32 cache layout and 50,257 FP32 logits.  Failure returns empty cache and logit arrays.  A failed call preserves the borrowed input cache and model, releases every allocation made by the call, and leaves the host at the preceding token position.

| Status | Meaning |
|-------:|---------|
| 0 | The operation succeeded. |
| 1 | The model length or header is invalid. |
| 2 | Model validation found an invalid coefficient, scale, or FP32 parameter. |
| 3 | The token, position, cache length, or cache finiteness check failed. |
| 4 | A quantizer input or returned cache/logit value is nonfinite. |

The token step checks model length and header, token and position bounds, cache length, and cache finiteness.  Each learned projection checks its FP32 input before quantizing it.  The step checks the returned cache and logits before returning success.  Whole-model parameter validation occurs when the session opens.

On a successful token call, the host replaces the old cache with the returned cache and releases the old cache and returned logits after reading them.  Reset releases the current cache and retains the validated model.  Close releases the cache and model.  A failed call leaves the old cache available for retry or reset.
