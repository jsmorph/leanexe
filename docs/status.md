# Development Status

This report describes the repository state on 2026-09-02.  Checked registries contain twenty source-driven Talos cases and twenty exact-artifact packages, while the demonstration index contains eleven current array-interface programs and the original scalar example.  The root [Development Plan](../plan.md) owns remaining work, while repository tools and registries own changing counts and release identities.

## Current capabilities

| Boundary | Current evidence |
|----------|------------------|
| Source compilation | LeanExe loads checked Lean declarations, accepts the subset in the [language specification](spec.md), and emits standalone WASM or one of the bounded WASI adapters. |
| Self-hosted binary emission | The ordinary library path freezes lowered modules as canonical images and uses the same pure emitter compiled into WebAssembly.  Wasmtime Stage 1 and JavaScript Stage 2 reproduce the complete emitter artifact and all twenty registered compiler artifacts byte for byte. |
| Execution | The execution suite compares accepted programs with ordinary Lean or the IR evaluator where those references apply, and runs generated modules with Wasmtime. |
| Source-driven proofs | `proofs/talos/cases.json` registers twenty cases.  Every case has a completed input-generic behavioral theorem, including all eight CLOB exports through `depth`, and the aggregate source-driven gate passed all twenty cases on 2026-08-26. |
| Exact-artifact proofs | `proofs/artifacts/registry.json` registers twenty frozen WASM packages.  Each package embeds exact bytes, decodes and validates them, proves translation equality with its Talos execution module, and connects that module to a behavioral theorem. |
| Artifact decoder | Checked decoder soundness connects successful complete-file decoding to an independent declarative grammar for the accepted Core 3.0 binary profile. |
| Artifact validator | Checked validator soundness connects accepted modules to the independent `CoreValid` judgment for the supported sections and instructions. |
| Proof generation | `leanexegen` generates a specification, source program, WASM artifact, annotations, and direct artifact proof for a fixed `Array UInt64 -> Array UInt64` interface.  Demo 12 independently verifies a bounded first-zero search whose found branch allocates and copies an array with one element removed. |
| Proof support | The compiler emits annotation schema 1, ProofKit supplies checked semantic lemmas and tactics, and the knowledge forest selects filtered entries from versioned LTG packages. |
| Stateful proving | `leanexegen` records accepted runs with distinct attempt identities and exact generated proof adapters.  A separate Codex task can compose selected package-local modules into one candidate, promotion checks its declarations and axioms, and a later run selects the resulting forest.  Live proving receives catalogs and checked sources without archived proof evidence; an accepted Demo 10 run used a Demo 9 worked example through this boundary. |
| Compiler theorems | Compiler-side scalar-certificate theorems prove agreement between selected IR emitters and the structured WASM instruction sequences used by annotation checks.  The current Phase 3 increment applies this path to the recurring zero-or-index-plus-one decoder.  A general source-to-WASM correctness theorem does not yet exist. |

The [Talos proof inventory](../proofs/talos/README.md) names each source-driven and artifact theorem.  [Artifact Proving](artifact-proving.md) explains how the exact binary remains the subject of the final theorem when annotations and compiler-derived evidence help construct the proof.  The proof packages can be checked without LeanExe, Codex, source code, or a compiler-correctness premise.

## Release state

`proofs/artifacts/release.json` is a draft record for release-input digest `5de9678970b1a9b74d50c1407457423a7fa6eabd3f430f56cfdc0e407af2b7e5` at source revision `0e0d752904fc90dee3ef3511ffab91f3d358c1ed`.  On 2026-08-26, the aggregate artifact proof passed all twenty packages, while the conformance gate completed with the configured imported-memory warning after 3,853 Talos passes, six known failures, 627 skips, no cascades, decoder errors, interpreter errors, or fuel exhaustion, fifteen expected invalid-module classifications, and twenty-five Wasmtime file passes.  `tools/artifact-release.js inspect` accepts the revision and both warm receipts, leaving the cold-checkout result as the sole unresolved condition.

Cold verification is deferred and does not form part of the current work.  The draft therefore makes no release-readiness claim, and `tools/artifact-release.js check-ready` continues to fail as designed.  A future cold-checkout run must repeat both release checks at the recorded revision before the record can become ready.

Lean 4.31.0 accepts the archived kernel-unsoundness reproduction referenced by the release record.  The owner accepted that toolchain defect for this project after the recorded narrow lexical audit of the artifact proof sources and two local LeanExe imports.  The audit does not repair the kernel or cover transitive dependencies.

## Known limits

| Area | Current limit |
|------|---------------|
| Source language | Programs must remain in the pure, monomorphic, first-order subset.  Public ABI values exclude recursive inductives and function values. |
| Arithmetic | `UInt64` follows wrapping arithmetic.  `Nat` is bounded by the compiler's runtime representation where it crosses executable code. |
| Floating point | Talos can execute `f64` instructions through native `Float`, but the exact-artifact profile and LeanExe source subset do not admit proof-grade floating-point programs.  The deferred [Proof-Grade `f64` Artifact Semantics](../plans/f64-artifact-semantics.md) plan defines the required binary64 semantics, artifact checks, and numerical-refinement layer. |
| Strings | Lean `String` is not a supported runtime value.  `LeanExe.AsciiString` and `ByteArray` provide the supported textual representations. |
| Heap updates | Generated programs may mutate freshly allocated or uniquely owned heap objects internally.  Public array inputs are borrowed, so an operation returning a changed array allocates a distinct result rather than overwriting the caller's array. |
| Compiler correctness | Exact-artifact proofs establish behavior directly from bytes.  Compiler theorems currently support selected emitted regions and proof-generation evidence rather than a complete source-to-artifact refinement theorem. |
| Talos conformance | The pinned Talos interpreter has six known failures for imported-memory limit handling in `memory_grow.wast`.  The artifact profile forbids imports, and the conformance gate reports the exact rows as an upstream warning. |
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
