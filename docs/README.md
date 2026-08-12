# Documentation

LeanExe documentation separates current behavior, development work, design records, and historical material.  The repository [README](../README.md) introduces the compiler, while [Developing LeanExe](../DEVELOPING.md) defines setup and test procedures.  The [development plan](../plan.md) remains the authoritative work queue, and the [development journal](../devnotes.md) records decisions and test results.

## Maintained Documentation

| Document | Purpose |
|----------|---------|
| [LeanExe User Manual](manual.md) | Source patterns, supported programming forms, diagnostics, and examples. |
| [Language Specification](spec.md) | Accepted language, ABI, memory model, numeric semantics, and unsupported behavior. |
| [Technical Summary](summary.md) | Compiler architecture, execution model, verification structure, and current boundaries. |
| [Architecture Diagram](leanexe.png) | High-level compilation, annotation, LTG, execution, and artifact-proof flow. |
| [Verifying a Program](verifying.md) | Procedure for registering, proving, and checking a Talos artifact. |
| [Artifact Verification Format](artifact-format.md) | Restricted WebAssembly binary profile, formal boundaries, artifact packages, manifests, and release evidence. |
| [`leanexegen` Headless Codex Orchestrator](leanexegen.md) | CLI stages, isolated Codex tasks, fixed formal interface, proof package, trust boundary, and current limitations. |
| [Structured LTG Catalog](ltg.md) | Canonical entries, category indexes, task filtering, package identity, fixed-artifact evidence, and scaling tests. |
| [LTG Metrics](ltg-metrics.md) | Counting model and dated inventory for categories, entries, declarations, tactics, coverage, and bytes. |
| [Artifact-Proof Strategies](proof-strategies.md) | Goal-directed guidance for control flow, frames, arrays, arithmetic, memory, allocation, and diagnosis. |
| [LeanExe Type Theory](typetheory.md) | Lean source theory, accepted executable fragment, runtime interpretation, and rejection boundary. |
| [Prime-Factor Artifact Walkthrough](../demos/demo-1/README.md) | Step-by-step prose request, generated Lean sources, artifact theorem, samples, and independent verification. |
| [Talos Imported-Memory Defect](telos-bug.md) | Reproduction, provenance, semantic cause, artifact-profile effect, and repair boundary for the imported-memory conformance failure. |
| [JSON Tree WASI Demo](demo.md) | End-to-end source, build, execution, and verification example. |

## Development Records

| Document | Purpose |
|----------|---------|
| [Development Status](status.md) | Current completion report, open proof obligations, risks, and next work. |
| [Proof Engineering Plan Notes](plan-notes.md) | Reusable proof assets, elaboration boundaries, failed approaches, and candidate lemmas. |
| [Reusable WASM Proof Library Plan](wasm-proofs.md) | Curated lemmas and tactics, distillation rules, Pi discovery, dependency controls, pilots, and validation gates. |
| [WebAssembly Annotation Sidecar](annotations.md) | Annotation design, checked recipe registry, iterative implementation, and measured proof evidence. |
| [Compiler-Theorem Bridge](compiler-theorem-bridge.md) | Direct and indirect uses of compiler theorems in exact-artifact proof generation. |
| [Faster Direct WASM Proof Generation](better-wasm-proving.md) | Technical analysis of proof boundaries, checked summaries, source guidance, certificates, and measurement. |
| [Opacity and Elaboration Boundaries](opacity-proof-boundaries.md) | Controlled experiments with compact semantic interfaces and opaque generated definitions. |
| [Implementation Reviews](reviews.md) | Dated assessments of toolchain, execution, and artifact-verification completeness. |
| [Development Journal](../devnotes.md) | Dated decisions, implementation records, references, and test results. |

## Design Records

| Document | Purpose |
|----------|---------|
| [Type Classes](typeclasses.md) | Static evidence specialization design and implementation criteria. |
| [Lean String Support](strings.md) | Unimplemented runtime `String` proposal and required work. |
| [Emitter Restructuring](emitter.md) | Emitter organization, implementation survey, increments, and validation plan. |
| [Module Guarantees](guarantees.md) | Guarantee inventory and required order of proof work. |

## Historical Documents

| Document | Purpose |
|----------|---------|
| [Archived Development Agenda](history/agenda.md) | Superseded work queue retained for old references. |
| [Original GCD Talos Experiment](history/leanexe-talos.md) | First generated-WASM verification experiment. |
| [Original Association-List Talos Experiment](history/leanexe-talos-assoc-list.md) | Early recursive-data verification experiment. |
| [CLOB Completion Snapshot](history/clob-completion-snapshot.md) | Archived pickup state at commit `8dd82fc`. |
| [`leanexegen` Origin Note](history/leanexegen-origin.md) | Original prose request and prime-factor example that initiated the orchestrator. |

The [demonstration index](../demos/README.md), [benchmark index](../benchmarks/README.md), [plan registry](../plans/README.md), and [paper index](../paper/README.md) cover material maintained outside `docs/`.  Those indexes state why each directory exists and identify the document that owns its current status.  Historical files retain old decisions and examples without becoming competing work queues.
