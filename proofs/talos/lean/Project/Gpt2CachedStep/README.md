# Pretrained GPT-2 cached-inference proofs

This directory proves exact execution of GPT-2 124M inference for a sequence
of up to 128 tokens.  It covers the twelve transformer blocks, attention
cache, final normalization, all 50,257 logits, allocation, and buffer
release. The current source-driven gate passed on 2026-09-24 against fresh
compiler output, including the retained-owner guards and revised loop frames.
The retained artifact package records the earlier 19,083-byte binary proof;
this source refresh does not revalidate that frozen binary identity.

The specification is the [Lean cached model](../../../../../LeanExe/Models/Gpt2/README.md).
Weights arrive as runtime bytes.  The proof accepts every correctly sized
weight array, including exceptional binary32 values.  The
[GPT guide](../../../../../docs/gpt/README.md) explains the goals and relates
this work to the tiny model's numerical proofs.

## Public proof sequence

| Theorem | Statement |
|---------|-----------|
| [Token step](Spec.lean), `Spec.cachedStep_exact` | A generated module call terminates with the exact Lean cache and logit bytes, a valid resulting heap, and preservation of protected input regions. |
| [Session](Session/Spec.lean), `Spec.gpt2_128_exact` | Starting from module initialization, reset, weight allocation, and byte input, up to 128 successive token calls return the Lean recurrence's cache and logits.  The sequence includes releases of preceding caches and returned logits. |
| [Binary artifact](ArtifactTranslation.lean), `Artifact.artifact_gpt2_128_exact` | The embedded binary decodes, satisfies the grammar, validates, and has the complete session behavior after translation to Talos. |

The token-step theorem assumes represented inputs, a valid heap, protected
weight and cache regions, a UInt64-representable position, and capacity for
accepted-path allocations.  It covers the four rejected-input paths:
weight length, token ID, position, and cache length.  Rejection returns
empty outputs with the store unchanged.

The session theorem derives the heap, ownership, representation, and
allocation premises from three input conditions: 497,759,232 weight bytes,
token IDs below 50,257, and at most 128 tokens.  It starts at position zero
with an empty cache and carries each returned cache into the next call,
using the same weights throughout.  This establishes the sequence represented
by the cache.  The standalone token step accepts any cache contents of the
required length and computes the specified result from those bytes.

The session's allocation argument uses
a 512 MiB initial heap-top allowance plus 16 MiB per token within the module's
4 GiB address limit.  The artifact theorem transfers that result to the
decoded binary through checked equality of execution models.

## Proof organization

| Files or directory | Responsibility |
|--------------------|----------------|
| [Generated module](Program.lean) and [layout facts](Layout.lean) | Name the instruction streams and establish model dimensions. |
| [Linear projection](LinearRows/Spec.lean), [normalization](LayerNorm/Spec.lean), and scalar proofs | Prove ordered binary32 operations, packed reads, loops, construction, and allocation. |
| [Cached attention](CachedAttention/Spec.lean) and [transformer block](CachedBlock/Spec.lean) | Compose kernel calls, cache updates, and temporary-buffer releases. |
| [Hidden traversal](CachedHidden/Spec.lean) and [vocabulary projection](Vocabulary/Spec.lean) | Compose embeddings, all twelve blocks, and the 50,257 output scores. |
| [Accepted entry](Entry/Accepted.lean) and [rejected entry](Entry/Rejected.lean) | Join validation, tensor computation, output ownership, and the public return. |
| [Session proof](Session/Spec.lean) | Connect initialization, input encoding, recurrent calls, and output releases. |
| [Artifact decoding](ArtifactDecode.lean), [validation](ArtifactValidation.lean), and [translation](ArtifactTranslation.lean) | Check the binary and connect it to the proved execution model. |

Execution equality uses Lean's logical Float32 arithmetic and Talos's WASM
semantics.  The runtime target uses Wasmtime with canonical NaNs.  The
[host and reference](../../../../../training/gpt2/README.md) implement
tokenization, sampling, and the native call sequence.  Those implementations
and Wasmtime remain outside the Lean proof.  Real-arithmetic error bounds
and formal agreement with the separate full-prefix algorithm remain open.

## Checking and evidence

The [checkpoint record](../../../../../data/gpt2-124m/README.md) gives setup,
runtime tests, measured errors, memory use, and completions.  From the
repository root, regenerate the source artifact and check its specification:

```sh
tools/talos-proof.js check gpt2_cached_step
```

Check the distributed binary against the embedded artifact and theorem:

```sh
tools/artifact-proof.js check \
  proofs/artifacts/gpt2_cached_step/e93de126e00d7f5c5b9b30ca014a13b1385e9f91e3cb6b4e56a4aacf7a2b4ade/program.wasm \
  Project.Gpt2CachedStep.ArtifactTranslation
```

The artifact check reads the frozen binary and its proof package.  The
source check regenerates compiler output and checks its execution model.
The CLI also compiles current source and reports that binary's hash with
`--json`.  Exact-byte coverage applies to the binary identified by the
artifact proof.  Both proof drivers use the repository's Lean runner.  The
[Talos guide](../../../README.md) describes the shared runtime proofs and
verification tools.
