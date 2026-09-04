# Development Status

This report describes the repository state on 2026-09-04.  The source-driven registry contains twenty-six Talos cases, all complete.  The separate exact-artifact registry contains twenty-one frozen packages, and the source-driven proof tree tracks one untrusted `Program.lean` execution cache for each of its twenty-six cases.  The demonstration index contains eleven current array-interface programs and the original scalar example.  The root [Development Plan](../plan.md) owns remaining work, while repository tools and registries own changing counts and release identities.

## Current capabilities

| Boundary | Current evidence |
|----------|------------------|
| Source compilation | LeanExe loads checked Lean declarations, accepts the subset in the [language specification](spec.md), and emits standalone WASM or one of the bounded WASI adapters. |
| Self-hosted binary emission | The experimental image path can freeze lowered modules and invoke the pure emitter compiled into WebAssembly.  Its retained Wasmtime Stage 1 and Stage 2 receipt reproduces the complete emitter artifact and all twenty compiler artifacts registered when that receipt was recorded, byte for byte.  Production compilation uses the direct native serializer, and self-hosting is not an aggregate gate. |
| Execution | The execution suite compares accepted programs with ordinary Lean or the IR evaluator where those references apply, and runs generated modules with Wasmtime. |
| Source-driven proofs | `proofs/talos/cases.json` registers twenty-six complete cases, and the proof tree tracks twenty-six corresponding `Program.lean` caches.  Five floating-point entries culminate in the guarded Euler Rusanov flux, with source, generated-WAT, big-step, explicit small-step, and numerical theorems at the applicable layers.  The sixth proves exact generated-WAT execution of the fixed two-cell step: three guarded flux calls, eight accepted-status decisions, six conservative updates, the seven pure-model result words, and complete store preservation.  The current twenty-six-case aggregate gate passes. |
| Exact-artifact proofs | `proofs/artifacts/registry.json` registers twenty-one frozen WASM packages.  Each package embeds exact bytes, decodes and validates them, proves translation equality with its Talos execution module, and connects that module to a behavioral theorem.  Euler is the first registered exact artifact to use the restricted binary64 profile. |
| Artifact decoder | Checked decoder soundness connects successful complete-file decoding to an independent declarative grammar for the accepted Core 3.0 binary profile. |
| Artifact validator | Checked validator soundness connects accepted modules to the independent `CoreValid` judgment for the supported sections and instructions. |
| Proof generation | `leanexegen` generates a specification, source program, WASM artifact, annotations, and direct artifact proof for a fixed `Array UInt64 -> Array UInt64` interface.  Demo 12 independently verifies a bounded first-zero search whose found branch allocates and copies an array with one element removed. |
| Proof support | The compiler emits annotation schema 1, ProofKit supplies checked semantic lemmas and tactics, and the knowledge forest selects filtered entries from versioned LTG packages. |
| Stateful proving | `leanexegen` records accepted runs with distinct attempt identities and exact generated proof adapters.  A separate Codex task can compose selected package-local modules into one candidate, promotion checks its declarations and axioms, and a later run selects the resulting forest.  Live proving receives catalogs and checked sources without archived proof evidence; an accepted Demo 10 run used a Demo 9 worked example through this boundary. |
| Compiler theorems | Compiler-side scalar-certificate theorems prove agreement between selected IR emitters and the structured WASM instruction sequences used by annotation checks.  The current Phase 3 increment applies this path to the recurring zero-or-index-plus-one decoder.  A general source-to-WASM correctness theorem does not yet exist. |

The [Talos proof inventory](../proofs/talos/README.md) names each source-driven and artifact theorem.  [Artifact Proving](artifact-proving.md) explains how the exact binary remains the subject of the final theorem when annotations and compiler-derived evidence help construct the proof.  The proof packages can be checked without LeanExe, Codex, source code, or a compiler-correctness premise.

## Release state

The proof workspace and `proofs/artifacts/release.json` now record exact Lean
4.34.0-rc2, Talos revision
`87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`, and the migrated release-input
identity.  The release record remains a draft for release-input digest
`de4761fc0d3b129d99dfdb239f0cec042df3962fbbf5de133c8ef11592fb1717`.
The prior aggregate artifact receipt no longer matches after the fixed-step
proof changes; aggregate artifact proof, semantic conformance, immutable source
revision, and cold checkout are the four current blockers.  The successful
2026-08-26 receipts likewise remain historical evidence for their earlier
digest rather than current release receipts.

The draft makes no release-readiness claim, and
`tools/artifact-release.js check-ready` continues to fail as designed.  The
conformance gate must still produce a receipt for the migrated inputs; an
immutable source revision must then be recorded, and a later cold-checkout run
must repeat both warm gates at that revision before the record can become ready.

Lean 4.31.0 accepts the archived kernel-unsoundness reproduction preserved by
the release record.  The owner accepted that older toolchain defect after the
recorded narrow lexical audit of the artifact proof sources and two local
LeanExe imports.  The audit does not repair the historical kernel or cover
transitive dependencies.  The current record separately identifies exact Lean
4.34.0-rc2 and records that the reproduction is rejected there; a new aggregate
artifact receipt remains pending for the current input identity.

## Known limits

| Area | Current limit |
|------|---------------|
| Source language | Programs must remain in the pure, monomorphic, first-order subset.  Public ABI values exclude recursive inductives and function values. |
| Arithmetic | `UInt64` follows wrapping arithmetic.  `Nat` is bounded by the compiler's runtime representation where it crosses executable code. |
| Floating point | Selected `UInt64` bit-pattern intrinsics lower to `f64.add`, `f64.mul`, and the two i64/f64 reinterpretations.  Their source-driven cases, and Euler's exact frozen artifact, have proof-grade Talos execution and numerical theorems.  General Lean `Float`, `f32`, binary64 division, square root, classification, and comparisons remain unsupported by the LeanExe and exact-artifact profiles. |
| Strings | Lean `String` is not a supported runtime value.  `LeanExe.AsciiString` and `ByteArray` provide the supported textual representations. |
| Heap updates | Generated programs may mutate freshly allocated or uniquely owned heap objects internally.  Public array inputs are borrowed, so an operation returning a changed array allocates a distinct result rather than overwriting the caller's array. |
| Compiler correctness | Exact-artifact proofs establish behavior directly from bytes.  Compiler theorems currently support selected emitted regions and proof-generation evidence rather than a complete source-to-artifact refinement theorem. |
| Talos conformance | The last accepted receipt has six known failures for imported-memory limit handling in `memory_grow.wast`.  The artifact profile forbids imports, and the historical conformance gate reports the exact rows as an upstream warning.  The 2026-09-04 current-input attempt matched all fifteen exact invalid-module classifications, then timed out while warming the pinned runner's broad Mathlib import closure; it emitted no conformance receipt. |
| Proof generation | Generation time remains variable and can exceed thirty minutes for structured loops.  Proof size, retrieval, revisions, checked abstraction use, and transfer across demos remain relevant measurements. |

## Immediate work

Demo 12 supplies the accepted structurally different artifact: its five loops implement early-exit search, allocation, prefix copy, and shifted-suffix copy.  ProofKit contains checked theorems for the compiler's one-word literal-key search, public erase-result reconstruction, and exact raw-cell prefix and shifted-suffix loops under symmetric source-target nonoverlap.  The compiler emits `leanexe.array.find-idx-eq.v1` and `leanexe.array.erase-copy.v1`, and the retained clean reproof covers the unchanged digest `7cdd8adba75d4f076d0a142f824a19a0d34d6a5cedd1a810a417a7fc5789f7b6`.

A separate `tools/leanexegen verify -s` invocation accepted the measured package before the follow-up ProofKit changes.  Stage 5 took 3,987.145392 seconds against the 3,907.231311-second baseline, an increase of 2.045 percent.  The proof decreased from 860 to 607 lines, 3,516 to 2,587 words, 39,249 to 28,874 bytes, and 47 to 38 journaled checks, reductions of 29.419, 26.422, 26.434, and 19.149 percent.  A current-ProofKit re-freeze later preserved the artifact digest and passed independent verification without running fresh proof generation or evaluating current LTG retrieval.

The reproof used seven LTG entries and rejected none.  `FixedArrayFindIdxEq.program_spec` and `FixedArrayCopy.eraseIdxProgram_spec` removed every local search, prefix-copy, and shifted-suffix loop invariant.  ProofKit now also contains the dynamic local length-store theorem and the encoded-index comparison fact identified by the journal.  Erase setup and branch-aware result transfer remain under review.

Phase 3 selected the compiler's zero-or-index-plus-one decoder because the same six-top-level-instruction region appears after the Demo 12 search, in ClobCancel, and twice in ClobDepth.  The compiler descriptor and certificate prove emitter agreement after successful IR recognition, while a separate annotation scanner records matching source, scratch-start, destination, and encoding roles.  The artifact consumer checks the complete nested instruction shape and generates a Lean equality to the neutral `EncodedIndexDecoder.program`.

The Demo 12 annotation pass preserved its 2,183-byte artifact and digest, generated the exact decoder equality, and passed separate package verification.  The pass reused the accepted behavior proof, so it measured neither LTG retrieval nor fresh proof generation.  The provisional LTG entry therefore records a checked capability rather than an accepted Demo 12 proof use.

The annotation consumer now emits a resolved-tail theorem for every version-two direct semantic recipe with an exact Lean program equality.  `proof-recipes.json` names that theorem in `direct.tailEquality`, while archived version-one recipes remain valid.  A current Demo 12 annotation pass generated tail theorems for the nested find-index, encoded-index, and erase-copy regions, preserved the artifact digest, and passed independent package verification.

ProofKit now exposes `EncodedIndexDecoder.resultFrame_get_ne`, `EncodedIndexDecoder.resultFrame_validIndex`, `FixedArrayAllocatorWindow.allocFrame_shape`, and `FixedArrayAllocatorWindow.allocFrame_validIndex`.  A fixed-artifact Demo 12 reproof retrieved and used the broader decoder getter, while the accepted source did not use either new allocator declaration.  Independent package verification accepted the resulting theorem over the unchanged artifact digest.

Stage 5 took 5,903.365887 seconds, and the accepted proof contains 1,059 lines and 50,046 bytes.  The result is slower and larger than the 3,371.682385-second, 735-line guided decoder-tail run, so it establishes capability and retrieval rather than a performance improvement.  Its journal records repeated work on opaque resolved suffixes, the encoded-option control path, dynamic erase setup, allocator getter reconstruction, and deeply nested continuation frames.

The ClobDepth compiler run preserved the registered 3,602-byte artifact and identified two matching decoder regions with different scratch and destination locals.  Its source proof now applies `EncodedIndexDecoder.program_spec` twice, removing four decoder-specific `wp_iff_cons` applications and four associated `wp_run` calls, while explicit region decomposition and premises produce a net increase of 21 source lines.  The complete `clob_depth` Talos proof gate passed, but this cross-program refactor has no comparable proof-generation-time measurement.
