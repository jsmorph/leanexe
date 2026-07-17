# Documentation

LeanExe documentation separates current behavior, development work, design records, and historical material.  The repository [README](../README.md) introduces the compiler, while [Developing LeanExe](../DEVELOPING.md) defines setup and test procedures.  The [development plan](../plan.md) remains the authoritative work queue, and the [development journal](../devnotes.md) records decisions and test results.

## Maintained Documentation

| Document | Purpose |
|----------|---------|
| [LeanExe User Manual](manual.md) | Source patterns, supported programming forms, diagnostics, and examples. |
| [Language Specification](spec.md) | Accepted language, ABI, memory model, numeric semantics, and unsupported behavior. |
| [Technical Summary](summary.md) | Compiler architecture, execution model, verification structure, and current boundaries. |
| [Verifying a Program](verifying.md) | Procedure for registering, proving, and checking a Talos artifact. |
| [JSON Tree WASI Demo](demo.md) | End-to-end source, build, execution, and verification example. |

## Development Records

| Document | Purpose |
|----------|---------|
| [Development Status](status.md) | Current completion report, open proof obligations, risks, and next work. |
| [Proof Engineering Plan Notes](plan-notes.md) | Reusable proof assets, elaboration boundaries, failed approaches, and candidate lemmas. |
| [Development Journal](../devnotes.md) | Dated decisions, implementation records, references, and test results. |

## Design Records

| Document | Purpose |
|----------|---------|
| [Type Classes](typeclasses.md) | Static evidence specialization design and implementation criteria. |
| [Lean String Support](strings.md) | Unimplemented runtime `String` proposal and required work. |

## Historical Documents

| Document | Purpose |
|----------|---------|
| [Archived Development Agenda](history/agenda.md) | Superseded work queue retained for old references. |
| [Original GCD Talos Experiment](history/leanexe-talos.md) | First generated-WASM verification experiment. |
| [Original Association-List Talos Experiment](history/leanexe-talos-assoc-list.md) | Early recursive-data verification experiment. |
