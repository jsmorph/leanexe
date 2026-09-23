# Quantized cached-inference proof

The registered `gpt2_quantized_cached` case contains `validateModel` and
`cachedStep` exports from the [quantized Lean model](../../../../../LeanExe/Models/Gpt2/Quantized/README.md).
Its candidate has 28,315 bytes and SHA-256
`9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075`.
The registration remains incomplete.

## Checked components

| Module | Result |
|--------|--------|
| [Generated execution model](Program.lean) | Talos translation of the candidate's generated WAT. |
| [Annotation matches](AnnotationMatches.lean) | Checked correspondence between compiler instruction regions and the generated model. |
| [FP32 helper region](FP32Region.lean) | Exact function and type renaming for twenty FP32 and runtime helpers from the frozen FP32 model. |
| [Projection helper region](ProjectionRegion.lean) | Exact function and type renaming for twelve quantized projection and runtime helpers. |
| [Layer normalization](LayerNorm.lean), [cached attention](CachedAttention.lean), [residual addition](AddRows.lean), and [GELU](Activate.lean) | Transported execution, ownership, allocation, and frame-preservation theorems for the unchanged FP32 operations. |
| [Internal grouped projection](GroupedProjection/Linear.lean) | Exact grouped output, owner return, allocation, temporary release, and preservation of protected buffers for the cached calling convention. |
| [Layout constants](Layout.lean) | Exact values and store preservation for model offsets, lengths, and cache-position size. |
| [Finite-word helper](Finite.lean) and [finite-word scan](FiniteWords.lean) | Exact FP32 finiteness tests and bounded scans, with unchanged store. |
| [Coefficient scan](Coefficients.lean) and [scale scan](Scales.lean) | Exact bounded validation and store preservation, including coefficient short-circuiting and eager scale reads. |
| [Model representation](Model.lean) | Accepted tensor predicates, block extents, and token coefficient and scale properties. |
| [Validator characterizations](../ProofKit/QuantizedValidity.lean) | Pointwise source conditions for finite words, permitted coefficients, and valid scales. |

Both region proofs establish portability and `FunctionRegion.Shift`, with
axiom audits containing only `propext`.  The shared runtime checks pin the
allocator, reset, retain, and release functions.  The internal projection
entry proof accounts for both borrowed owners and the returned owner slot.
The [raw-word quantization error proof](../ProofKit/QuantizedError.lean)
establishes nearest-even half-unit error and a reconstruction bound under
explicit division and clipping assumptions.

## Remaining proof and evaluation

The complete proof must cover initialization validation, the represented
model, checked projection calls, all block and step branches, temporary
release, cached sessions, address bounds, and a concrete memory bound.  The
resulting theorem must then transfer to the exact decoded binary.  No
complete-model execution or binary theorem is claimed here.

The [evaluation record](../../../../../data/gpt2-quantized-v1/README.md)
contains the retained grouped binary, all 6,432,896 bitwise logit comparisons,
cache comparisons, repeated memory and timing measurements, nine compiled
completions, and error diagnosis.  Exact agreement with the
quantized reference coexists with substantial differences from FP32 output.

```sh
tools/talos-artifact.js prepare gpt2_quantized_cached
tools/leanrun --timeout 3m --lock-timeout 5 lake -d proofs/talos/lean build Project.Gpt2QuantizedCached.FP32Region Project.Gpt2QuantizedCached.ProjectionRegion Project.Gpt2QuantizedCached.AnnotationMatches Project.Runtime.Checks
tools/leanrun --timeout 3m --lock-timeout 5 lake -d proofs/talos/lean build Project.ProofKit.QuantizedValidity Project.Gpt2QuantizedCached.Finite
```
