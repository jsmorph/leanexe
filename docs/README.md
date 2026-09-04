# Documentation

LeanExe assigns one subject to each maintained document.  The repository [README](../README.md) introduces the system, [Developing LeanExe](../DEVELOPING.md) owns setup and tests, and the root [Development Plan](../plan.md) owns unfinished work.  The development journal records rationale and test evidence without serving as current guidance.

## Language and compiler

| Document | Authority |
|----------|-----------|
| [LeanExe User Manual](manual.md) | Source patterns, examples, diagnostics, and authoring guidance. |
| [Language Specification](spec.md) | Accepted Lean subset, numeric semantics, ABI, memory representation, ownership rules, and rejection boundaries. |
| [LeanExe Type Theory](typetheory.md) | Relationship among Lean's source theory, the executable fragment, runtime values, and artifact propositions. |
| [Compiler Architecture](compiler.md) | Extraction, specialization, IR, ownership analysis, WASM emission, annotations, and compiler theorem boundaries. |
| [Self-Hosted WebAssembly Emitter](self-hosted-emitter.md) | Canonical final-module image, host ABI, precise self-hosting claim, compatibility rules, and bootstrap receipt. |
| [Architecture Diagram](leanexe.png) | High-level source, compilation, annotation, LTG, execution, and proof flow. |
| [JSON Tree WASI Example](demo.md) | Source, compilation, command execution, and verification for a typed tree-processing program. |

## Artifact verification and proving

| Document | Authority |
|----------|-----------|
| [Artifact Verification Format](artifact-format.md) | Restricted binary profile, exact-byte packages, decoding, validation, theorem boundary, and release evidence. |
| [Verifying a Program](verifying.md) | Procedure for creating, registering, proving, and independently checking an artifact package. |
| [Artifact Proving](artifact-proving.md) | Relationship among Talos, ProofKit, compiler annotations, LTG retrieval, generated proof work, and independent checking. |
| [`leanexegen` Reference](leanexegen.md) | CLI stages, task isolation, fixed public interface, proof packages, verification, and reproving. |
| [WebAssembly Annotations](annotations.md) | Implemented sidecar schema, recognized regions, generated checked declarations, and recipe selection. |
| [Knowledge Forest and Structured LTG](ltg.md) | Package and catalog schemas, forest selection, filtering, checked declarations, learning phases, exclusions, and task snapshots. |
| [LTG Metrics](ltg-metrics.md) | Reproducible measurements of catalog structure, declarations, tactics, coverage, and content size. |
| [Artifact-Proof Strategies](proof-strategies.md) | General proof-construction and diagnosis guidance that applies across artifact families. |
| [Talos Imported-Memory Defect](telos-bug.md) | Reproduction, semantic cause, conformance warning, artifact-profile effect, and upstream repair boundary. |

## Status and evidence

| Document | Authority |
|----------|-----------|
| [Development Status](status.md) | Current checked capabilities, known limitations, and release state. |
| [LTG and CLOB Retrospective](retro-1.md) | Measured LTG results, structured-retrieval limits, CLOB findings, and the relationship between them. |
| [Development Plan](../plan.md) | Ordered active work and completion conditions. |
| [Detailed Plans](../plans/README.md) | Technical plans for unfinished work referenced by the root roadmap. |
| [Proof-Grade `f64` Artifact Semantics](../plans/f64-artifact-semantics.md) | Active plan for exact binary64 artifact execution, finite-result safety, numerical refinement, and checked certificates. |
| [Talos Proof Inventory](../proofs/talos/README.md) | Registered source-driven and exact-artifact theorem inventory. |
| [Demonstrations](../demos/README.md) | Twelve end-to-end programs and their retained proof packages. |
| [Benchmark Evidence](../benchmarks/README.md) | Proof-generation runs, journals, telemetry, and acceptance results. |
| [Research Papers](../paper/README.md) | Publication sources, PDFs, and marXiv records. |

Proof journals, benchmark runs, `devnotes.md`, and published papers preserve evidence or research records.  They may contain observations tied to an older artifact, proof interface, or tool version.  Current behavior comes from the references above and the checked implementation.
