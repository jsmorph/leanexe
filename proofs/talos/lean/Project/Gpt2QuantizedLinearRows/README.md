# Quantized GPT-2 projection proof

The completed `gpt2_quantized_linear_rows` case proves the [quantized projection](../../../../../LeanExe/Models/Gpt2/Quantized/Kernel.lean) against its exact 4,741-byte WASM binary.  The [implementation plan](../../../../../plans/gpt2-quantized.md) places cached-model integration after this projection milestone.

## Arithmetic and instructions

Weights and row activations use signed bytes in `[-127,127]`.  The [quantizer proof](../ProofKit/QuantizedValue.lean) excludes reserved byte `0x80`.  The [source projection lemmas](Source.lean) establish packed sizes, scale reads, activation reads, and exact integer accumulation at every reduction prefix of length at most 3,072.  The absolute accumulator bound is `length * 16129`, at most 49,548,288.

| Source operation | Emitted instruction | Checked source correspondence |
|------------------|---------------------|-------------------------------|
| `Float32.nearestBits` | `f32.nearest` | [Nearest-even rounding](../ProofKit/F32Nearest.lean) |
| `Float32.toInt32Bits` | `i32.trunc_sat_f32_s` | [Saturating conversion](../ProofKit/F32TruncSat.lean) |
| `Float32.ofInt32Bits` | `f32.convert_i32_s` | [Signed integer conversion](../ProofKit/F32Convert.lean) |
| `Signed32.extend8Bits` | `i32.extend8_s` | [Signed byte extension](../ProofKit/SignedByte.lean) |

All four correspondence theorems quantify over every raw 32-bit input.  The compiler represents scalar words in `i64` values.  Its `UInt32` addition and multiplication use `i64` operations followed by a 32-bit mask.  The [accumulation proof](../ProofKit/QuantizedInt32.lean) identifies this modular recurrence with the mathematical signed sum under the prefix bounds.  The integer-to-FP32 conversion can round, and the source fixes each subsequent FP32 multiplication and bias addition.

The binary syntax, decoder, declarative grammar, validator, translation, and instruction equality support all four added instructions.  Their shared soundness proofs and focused parser/type tests pass.  Updating that profile changes the verifier-source identity recorded in artifact manifests.

## Generated functions and proof status

| Index | Function | Status |
|------:|----------|--------|
| 0 | Packed FP32 word read | Existing shared instruction pattern. |
| 1 | Row scale | Exact execution and complete store preservation proved. |
| 2 | Scalar quantization | Exact execution and complete store preservation proved. |
| 3 | Packed activation bytes and scales | Exact execution, allocation, ownership, and input preservation proved. |
| 4 | Signed dot product | Exact execution, store preservation, and source accumulator range proved. |
| 5, 7 | Quantized-row field selection | Exact execution and complete store preservation proved. |
| 6 | FP32 rescaling | Exact execution and complete store preservation proved. |
| 8 | Projection entry | Complete exact execution, allocation, ownership, temporary release, and input preservation proved. |
| 9–12 | Allocate, reset, retain, and release | Shared runtime equalities registered. |

The [byte generation loop theorem](../ProofKit/PackedByteGenerateLoop.lean) proves termination, exact output bytes, and writes confined to the destination under explicit address and page bounds.  The [complete row-quantizer theorem](Rows.lean) composes both allocations and construction loops.  It proves ownership and separation of the returned byte and scale buffers, preserves protected inputs, and records the resulting heap and memory capacity.  Its assumptions cover represented input, dimensions, free-list validity, and room for either allocation when reuse fails.  The source's `linearChecked` wrapper and its status and failure-cleanup behavior require an additional execution theorem.

The [row-scale buffer loop](ScaleLoop.lean) composes the row-scale helper with packed word generation.  The [activation-byte loop](ByteLoop.lean) composes input and scale reads with scalar quantization.  Both reuse the shared heap and packed-buffer proofs.

The [projection output loop](ProjectionLoop.lean) computes each specified dot product, reads both scales, applies FP32 rescaling and optional bias, and writes the exact result bytes.  The [output allocation theorem](ProjectionAllocate.lean) includes free-block reuse and memory growth while preserving all three source buffers.  The [return-path theorem](ProjectionRelease.lean) releases the activation and scale owners, preserves output ownership, and returns its pointer and length.

The [entry theorem](Linear.lean) composes quantization, output construction, and temporary release.  Its assumptions cover represented input buffers, dimensions, protected regions, heap validity, and sufficient allocation capacity.  The heap counters increase by three allocations, two releases, and two frees, with no retains.  The output remains owned by the caller.

The [exact-binary theorem](ArtifactTranslation.lean), `artifact_linearRows_exact`, proves decoding, grammar membership, validation, `CoreValid`, and the complete entry specification for the decoded binary.  The [frozen package](../../../../artifacts/gpt2_quantized_linear_rows/44c390d9605c8eea42b8509dcb7b367a354f2cb62df7158e59c071f87c4e3fc3/manifest.json) identifies SHA-256 `44c390d9605c8eea42b8509dcb7b367a354f2cb62df7158e59c071f87c4e3fc3`.  The [projection measurements](../../../../../data/gpt2-quantized-v1/README.md) retain the earlier compiler output.  The current package includes the I/O merge's removal of unused loop-flag stores.  The focused source gate and independent artifact check passed.  The theorem audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

```sh
tools/talos-artifact.js prepare gpt2_quantized_linear_rows
tools/talos-proof.js check gpt2_quantized_linear_rows
tools/artifact-proof.js check proofs/artifacts/gpt2_quantized_linear_rows/44c390d9605c8eea42b8509dcb7b367a354f2cb62df7158e59c071f87c4e3fc3/program.wasm Project.Gpt2QuantizedLinearRows.ArtifactTranslation
```

The full cached model has a [complete session proof](../Gpt2QuantizedCached/README.md).  A separate theorem for the standalone `linearChecked` wrapper remains open.
