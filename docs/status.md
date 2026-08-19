# Development Status

This report describes the repository state on 2026-08-18.  Checked registries contain twenty source-driven Talos cases and twenty exact-artifact packages, while the demonstration index contains eleven current array-interface programs and the original scalar example.  The root [Development Plan](../plan.md) owns remaining work, while repository tools and registries own changing counts and release identities.

## Current capabilities

| Boundary | Current evidence |
|----------|------------------|
| Source compilation | LeanExe loads checked Lean declarations, accepts the subset in the [language specification](spec.md), and emits standalone WASM or one of the bounded WASI adapters. |
| Execution | The execution suite compares accepted programs with ordinary Lean or the IR evaluator where those references apply, and runs generated modules with Wasmtime. |
| Source-driven proofs | `proofs/talos/cases.json` registers twenty cases.  Every case has a completed input-generic behavioral theorem, including all eight CLOB exports through `depth`. |
| Exact-artifact proofs | `proofs/artifacts/registry.json` registers twenty frozen WASM packages.  Each package embeds exact bytes, decodes and validates them, proves translation equality with its Talos execution module, and connects that module to a behavioral theorem. |
| Artifact decoder | Checked decoder soundness connects successful complete-file decoding to an independent declarative grammar for the accepted Core 3.0 binary profile. |
| Artifact validator | Checked validator soundness connects accepted modules to the independent `CoreValid` judgment for the supported sections and instructions. |
| Proof generation | `leanexegen` generates a specification, source program, WASM artifact, annotations, and direct artifact proof for a fixed `Array UInt64 -> Array UInt64` interface.  Demo 12 independently verifies a bounded first-zero search whose found branch allocates and copies an array with one element removed. |
| Proof support | The compiler emits annotation schema 1, ProofKit supplies checked semantic lemmas and tactics, and the knowledge forest selects filtered entries from versioned LTG packages. |
| Stateful proving | `leanexegen` records accepted runs with distinct attempt identities and exact generated proof adapters.  A separate Codex task can compose selected package-local modules into one candidate, promotion checks its declarations and axioms, and a later run selects the resulting forest.  Live proving receives catalogs and checked sources without archived proof evidence; an accepted Demo 10 run used a Demo 9 worked example through this boundary. |
| Compiler theorems | Compiler-side scalar-certificate theorems prove agreement between selected IR emitters and the structured WASM instruction sequences used by annotation checks.  A general source-to-WASM correctness theorem does not yet exist. |

The [Talos proof inventory](../proofs/talos/README.md) names each source-driven and artifact theorem.  [Artifact Proving](artifact-proving.md) explains how the exact binary remains the subject of the final theorem when annotations and compiler-derived evidence help construct the proof.  The proof packages can be checked without LeanExe, Codex, source code, or a compiler-correctness premise.

## Release state

`proofs/artifacts/release.json` is a draft record for release-input digest `612fbab1fa3c91e7a977799a9f46cd151a0de1d898abcfa314927c691cdf2ef5` at source revision `0b09cf0ee3e2f11decd64815130677ca147542e8`.  The aggregate artifact proof passed all twenty packages on 2026-08-13, and the conformance gate passed with the configured imported-memory warning after 3,853 Talos passes, six known failures, 627 skips, and twenty-five Wasmtime file passes.  `tools/artifact-release.js inspect` accepts both receipts and reports one unresolved condition: the cold-checkout result.

Cold verification is deferred and does not form part of the current work.  The draft therefore makes no release-readiness claim, and `tools/artifact-release.js check-ready` continues to fail as designed.  A future cold-checkout run must repeat both release checks at the recorded revision before the record can become ready.

Lean 4.31.0 accepts the archived kernel-unsoundness reproduction referenced by the release record.  The owner accepted that toolchain defect for this project after the recorded narrow lexical audit of the artifact proof sources and two local LeanExe imports.  The audit does not repair the kernel or cover transitive dependencies.

## Known limits

| Area | Current limit |
|------|---------------|
| Source language | Programs must remain in the pure, monomorphic, first-order subset.  Public ABI values exclude recursive inductives and function values. |
| Arithmetic | `UInt64` follows wrapping arithmetic.  `Nat` is bounded by the compiler's runtime representation where it crosses executable code. |
| Strings | Lean `String` is not a supported runtime value.  `LeanExe.AsciiString` and `ByteArray` provide the supported textual representations. |
| Heap updates | Generated programs may mutate freshly allocated or uniquely owned heap objects internally.  Public array inputs are borrowed, so an operation returning a changed array allocates a distinct result rather than overwriting the caller's array. |
| Compiler correctness | Exact-artifact proofs establish behavior directly from bytes.  Compiler theorems currently support selected emitted regions and proof-generation evidence rather than a complete source-to-artifact refinement theorem. |
| Talos conformance | The pinned Talos interpreter has six known failures for imported-memory limit handling in `memory_grow.wast`.  The artifact profile forbids imports, and the conformance gate reports the exact rows as an upstream warning. |
| Proof generation | Generation time remains variable and can exceed thirty minutes for structured loops.  Proof size, retrieval, revisions, checked abstraction use, and transfer across demos remain relevant measurements. |

## Immediate work

Demo 12 supplies the accepted structurally different artifact: its five loops implement early-exit search, allocation, prefix copy, and shifted-suffix copy.  ProofKit now contains a checked execution theorem for the compiler's one-word, literal-key `findIdx?` loop and a generic theorem that reconstructs `Array.eraseIdx!` from the final prefix and shifted-suffix reads.  The compiler emits `leanexe.array.find-idx-eq.v1`, and an independently verified annotation package identifies the frozen Demo 12 interval as `FixedArrayFindIdxEq.program 8 0`; a fresh fixed-artifact reproof remains pending.  The subsequent work will evaluate that support, inspect the residual erase proof, and continue one narrow compiler-theorem-directed experiment.
