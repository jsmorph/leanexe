# Quantized cached-inference proof

The registered `gpt2_quantized_cached` case contains `validateModel` and
`cachedStep` exports from the [quantized Lean model](../../../../../LeanExe/Models/Gpt2/Quantized/README.md).
Its verified binary has 28,315 bytes and SHA-256
`9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075`.
The source-driven and independent exact-binary gates pass.  The combined
`Artifact.artifact_gpt2_128_exact` theorem connects grammar membership,
decoding, validation, `CoreValid`, and the complete cached session.

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
| [Header validation](Header.lean) | Exact format-header acceptance with short-circuit field reads and unchanged store. |
| [Projection allocation budget](GroupedProjection/Budget.lean) | Sufficient address and page bounds for the scale buffer, byte buffer, and projection output. |
| [Quantized embedding](Embedding/Spec.lean) | Exact signed-byte decoding, FP32 rescaling and position addition, packed output ownership, and protected-buffer preservation. |
| [Block validation](BlockValidation.lean) | Exact acceptance for all thirteen coefficient, scale, and FP32 regions, with unchanged store. |
| [Block allocation budget](CachedBlock/Budget.lean) and [execution bound](CachedBlock/ExecutionBudget.lean) | Sufficient capacity and a heap-top bound within 96 KiB of the initial heap top for every success and failure path, at positions below 128. |
| [Block normalization](CachedBlock/Normalized.lean), [QKV projection](CachedBlock/Qkv.lean), and [cached attention](CachedBlock/Attention.lean) | Exact calls, output ownership, and frame preservation. |
| [Attention projection](CachedBlock/Projection.lean), [expansion](CachedBlock/Expanded.lean), and [contraction](CachedBlock/Projected2.lean) | Checked offsets, quantized calls, three allocations, temporary releases, and exact outputs. |
| [Residual addition](CachedBlock/Residual.lean), [second normalization](CachedBlock/Normalized2.lean), [GELU](CachedBlock/Activated.lean), and [hidden output](CachedBlock/Hidden.lean) | Exact FP32 calls and preservation of earlier live bindings. |
| [Finiteness checks](CachedBlock/FiniteTest.lean) and [cache construction](CachedBlock/Cache.lean) | All four rejection predicates, cache allocation and copying, and preservation of the successful status. |
| [Complete transformer block](CachedBlock/Spec.lean) | Exact source status, hidden and cache bytes, all four finite-value branches, protected-input preservation, and temporary-buffer cleanup. |
| [Cached traversal source](CachedHidden/Source.lean) and [size invariant](CachedHidden/Sizes.lean) | Twelve-layer recurrence, status propagation, 3,072-byte successful hidden output, and 73,728 appended cache bytes.  Failure returns status four and empty outputs. |
| [Traversal embedding](CachedHidden/Embedding.lean), [block call](CachedHidden/LayerCall.lean), and [update append](CachedHidden/LayerAppend.lean) | Exact compiled calls, returned status, cache-update allocation and copying, and preserved traversal bindings. |
| [Traversal control](CachedHidden/LayerControl.lean), [guarded releases](CachedHidden/LayerRelease.lean), and [skipped iteration](CachedHidden/InactiveStep.lean) | Checked counter advance, release-counter writes, retained-alias guards, and complete store preservation after a nonzero status. |
| [Active iteration](CachedHidden/ActiveStep.lean) and [allocation budget](CachedHidden/LayerBudget.lean) | Complete block call, update append, status-dependent cache release, previous-buffer releases, counter advance, and preserved owned outputs. |
| [Complete layer loop](CachedHidden/LayerLoop.lean) and [traversal allocation bound](CachedHidden/TraversalBudget.lean) | All twelve iterations, exact successful and failed source states, ownership preservation, termination, and heap-top growth of at most 1,659,552 bytes before final cache construction. |
| [Final-output preparation](CachedHidden/FinishPrepare.lean), [failure guard](CachedHidden/FinishGuard.lean), and [cache append](CachedHidden/FinishAppend.lean) | Exact branch selection, empty failed outputs, successful cache concatenation, and returned buffer assignments. |
| [Complete cached hidden function](CachedHidden/Spec.lean) and [allocation bound](CachedHidden/Budget.lean) | Exact callable function 58, embedding and twelve-layer traversal, status propagation, final cache construction, returned bytes, owned outputs, complete temporary cleanup, and heap-top growth bounded by incoming cache bytes plus 1,736,456. |
| [Token-step hidden call](Entry/Hidden.lean), [final normalization](Entry/Normalized.lean), and [vocabulary projection](Entry/Logits.lean) | Exact calls, status and buffer assignments, preserved live bindings, and the 50,257-logit output. |
| [Entry input test](Entry/InputTest.lean), [cache test](Entry/CacheTest.lean), [normalized guard](Entry/FiniteGuard.lean), and [output guard](Entry/OutputGuard.lean) | Header and input rejection, bounded cache-length arithmetic, all finite-word probes, short-circuit output checks, and preserved live owners. |
| [Complete session](Spec.lean) | Reset, checkpoint allocation and byte loading, model validation, up to 128 token calls, status-dependent termination, replaced-cache and logit release, and session shutdown. |
| [Token-step budget](Entry/Budget.lean) | Allocation sufficiency and heap-top growth bounded by incoming cache bytes plus 1,942,544.  The session allows 16 MiB per token from a 128 MiB initial allowance. |
| [Complete public token step](Entry/Public.lean) | Exact status, cache and logit bytes for public function 61, arbitrary 64-bit token masking, all input and numerical rejection branches, ownership, protected-input preservation, and temporary cleanup. |
| [Result assignment and return](Entry/Result.lean) | Exact status, cache and logit result words, and empty failed outputs. |
| [Model representation](Model.lean) and [source validation](ModelSource.lean) | Accepted tensor predicates, block extents, token coefficient and scale properties, and equivalence between validation status zero and the complete representation predicate. |
| [Public model validator](Validation/Public.lean) | Exact status, termination, and unchanged store for every represented input, including header rejection, global checks, and the early-exit twelve-block scan. |
| [Validator characterizations](../ProofKit/QuantizedValidity.lean) | Pointwise source conditions for finite words, permitted coefficients, and valid scales. |

Both region proofs establish portability and `FunctionRegion.Shift`, with
axiom audits containing only `propext`.  The shared runtime checks pin the
allocator, reset, retain, and release functions.  The internal projection
entry proof accounts for both borrowed owners and the returned owner slot.
The [scalar reconstruction bound](../ProofKit/QuantizedScalarError.lean)
combines nearest-even half-unit error with explicit quotient-rounding and
clipping terms.  It assumes finite input and scale words, a positive decoded
scale, and a stated bound on the exact scaled quotient.  The
[rescaling bound](../ProofKit/QuantizedRescaleError.lean) includes both FP32
multiplications under stated product-range bounds.  Every permitted
64-coordinate accumulator converts to FP32 exactly because its magnitude is
at most 1,032,256.  The native Lean export checker accepts every checkpoint coefficient, scale,
and retained FP32 word.  [Conditional forward bounds](Numerical/README.md) cover
every stage of the twelve-layer cached recurrence and every returned logit.
Checked range records cover all captured activation quantizers and 11,450
normalizations, 16,883,712 GELU inputs, and 5,496 attention calls from both models.
Projection range evaluation and evaluation of the propagated bound remain open.

## Verification and numerical work

The complete source session theorem passes with `propext`, `Classical.choice`,
and `Quot.sound`.  Its input assumptions are the 127,695,972-byte model shape
and at most 128 requested tokens.  Validation rejection closes the loaded
model.  Token-step failure ends the trace and releases the preceding cache
and weights.  Successful completion releases the final cache and weights.
The formal boundary includes host byte loading and the specified sequence of
WASM calls.  The exact-binary package transfers the complete specification
to the decoded module.  External-byte equality, all sixty-six function
bodies, validation, translation, and the declaration audit pass.  The audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

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

The frozen package can be checked independently with:

```sh
tools/artifact-proof.js check proofs/artifacts/gpt2_quantized_cached/9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075/program.wasm Project.Gpt2QuantizedCached.ArtifactTranslation
```
