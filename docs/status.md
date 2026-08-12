# Development Status

This report describes the repository state on 2026-08-11.  Checked registries contain twenty source-driven Talos cases and twenty exact-artifact packages, while the demonstration index contains ten current array-interface programs and the original scalar example.  The root [Development Plan](../plan.md) owns remaining work, while repository tools and registries own changing counts and release identities.

## Current capabilities

| Boundary | Current evidence |
|----------|------------------|
| Source compilation | LeanExe loads checked Lean declarations, accepts the subset in the [language specification](spec.md), and emits standalone WASM or one of the bounded WASI adapters. |
| Execution | The execution suite compares accepted programs with ordinary Lean or the IR evaluator where those references apply, and runs generated modules with Wasmtime. |
| Source-driven proofs | `proofs/talos/cases.json` registers twenty cases.  Every case has a completed input-generic behavioral theorem, including all eight CLOB exports through `depth`. |
| Exact-artifact proofs | `proofs/artifacts/registry.json` registers twenty frozen WASM packages.  Each package embeds exact bytes, decodes and validates them, proves translation equality with its Talos execution module, and connects that module to a behavioral theorem. |
| Artifact decoder | Checked decoder soundness connects successful complete-file decoding to an independent declarative grammar for the accepted Core 3.0 binary profile. |
| Artifact validator | Checked validator soundness connects accepted modules to the independent `CoreValid` judgment for the supported sections and instructions. |
| Proof generation | `leanexegen` generates a specification, source program, WASM artifact, annotations, and direct artifact proof for a fixed `Array UInt64 -> Array UInt64` interface. |
| Proof support | The compiler emits annotation schema 1, ProofKit supplies checked semantic lemmas and tactics, and structured LTG selects bounded task material from a categorized catalog. |
| Compiler theorems | Compiler-side scalar-certificate theorems prove agreement between selected IR emitters and the structured WASM instruction sequences used by annotation checks.  A general source-to-WASM correctness theorem does not yet exist. |

The [Talos proof inventory](../proofs/talos/README.md) names each source-driven and artifact theorem.  [Artifact Proving](artifact-proving.md) explains how the exact binary remains the subject of the final theorem when annotations and compiler-derived evidence help construct the proof.  The proof packages can be checked without LeanExe, Codex, source code, or a compiler-correctness premise.

## Release state

`proofs/artifacts/release.json` is a draft record for the current release-input digest, `23b34f98bc9da1c9c6e3801af0c20303380f3beacf45d0e1c3c2c678ddadef35`.  The aggregate artifact proof passed all twenty packages on 2026-08-11, and the conformance gate passed with the configured imported-memory warning after 3,853 Talos passes, six known failures, 627 skips, and twenty-five Wasmtime file passes.  `tools/artifact-release.js inspect` accepts both receipts and reports two unresolved conditions: the immutable source revision and its cold-checkout result.

The next commit will supply the immutable revision for the cold-checkout gate.  That gate will repeat both release checks in a detached repository-local checkout and write the final receipt.  `tools/artifact-release.js check-ready` determines whether the resulting record has any unresolved condition.

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

The release record must now be refreshed and its warm gates rerun against the settled documentation tree.  The next proof-engineering experiment should freeze a fold with a structurally different control or accumulator shape before receiving current annotation and LTG support.  The compiler-theorem work should then test one narrow theorem-directed artifact-proof boundary whose checked evidence remains useful without assuming complete compiler correctness.
