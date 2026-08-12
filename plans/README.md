# Plans

The root [Development Plan](../plan.md) remains the authoritative compiler and CLOB work queue.  This directory contains bounded verification and proof-generation plans whose status differs from that broader queue.  Each plan states its own evidence and completion conditions.

| Plan | Status | Scope |
|------|--------|-------|
| [Artifact-level verification](artifact-verification.md) | Core implementation and warm gates complete.  Immutable-revision cold-checkout evidence remains. | Exact bytes, decoder, validator, Talos translation, artifact registry, behavioral theorem, conformance, and release evidence. |
| [Artifact-proof composition](artifact-proof-composition.md) | Active.  All structured-tactic gates pass, with one structurally different fold still required before broader promotion. | Frame equality, fold completion, generated adapters, tactic retrieval, and controlled proof screens. |
| [Better direct WASM proving](better-wasm-proving.md) | Reference roadmap and experiment record.  Later annotation, structured-LTG, and composition documents supersede parts of its unchecked queue. | Proof workbenches, semantic summaries, source guidance, capsules, target certificates, and remote Lean capacity. |
| [Source-theorem transport](theorem-transport.md) | Deferred roadmap. | A source-dependent theorem connected through proof-grade IR semantics and verified lowering to exact artifact bytes. |

The [annotation design and evidence record](../docs/annotations.md) owns the implemented compiler-to-proof sidecar work.  The [structured LTG documentation](../docs/ltg.md) owns the current retrieval design, and the [LTG metrics report](../docs/ltg-metrics.md) owns its measured inventory.  New work should update the narrow plan that owns its acceptance gate rather than create another unordered root note.
