# Detailed Plans

The root [Development Plan](../plan.md) is the only active work queue.  This directory contains a detailed technical plan when an unfinished item needs more design than the root queue should carry.  Completed implementation plans and experiment sequences are removed after their current facts enter reference documentation and their remaining tasks enter the root plan.

| Plan | Status | Scope |
|------|--------|-------|
| [Full Lean kernel checker](lean-kernel-checker.md) | M0.0 complete; M0.1 next | Build a full Lean kernel checker in LeanExe through small runnable checkpoints. |
| [Verified tiny transformer inference](tiny-transformer.md) | Active; expands phase 14 | Build runnable FP64 exponential and softmax components, then trained tiny-model inference with numerical bounds. |
| [Self-Hosted WebAssembly Emitter](self-hosted-emitter.md) | Completed experimental milestone; optional regression path | Records canonical final-module serialization and exact self-reproduction without blocking native compiler development. |
| [Source-Theorem Transport](theorem-transport.md) | Deferred pending smaller compiler-theorem experiments | Connect a Lean source theorem through proof-grade IR semantics and verified lowering to a theorem about exact artifact bytes. |
| [Proof-Grade Floating-Point Artifact Semantics](f64-artifact-semantics.md) | Active; expands phase 7 of the root plan | Integrate Talos's proof-visible IEEE arithmetic through LeanExe's exact binary boundary, restricted bit-pattern intrinsics, and generated numerical-kernel proofs. |
| [Verified Euler Rusanov Data](euler-rusanov.md) | Active on `talosfp-euler`; expands phase 8 of the root plan | Prove a guarded binary64 one-dimensional Euler Rusanov kernel, exact WAT and binary behavior, and checked Sod data. |
| [800-grid Riemann run on dev](euler-riemann-dev.md) | Active; expands phase 11 of the root plan | Retain the 192-grid experiment and add a checked 800-grid calculation with streamed records and final figures. |
| [Euler certificates, completion, and convergence](euler-certificates-and-convergence.md) | Active on `main`; expands phase 13 of the root plan | Prove and execute numerical certificates, then investigate successful completion and continuum convergence in order. |

The active near-term compiler-theorem work appears in phase 3 of the root plan.  [Compiler Architecture](../docs/compiler.md) defines the current implemented theorem boundary, while [Artifact Proving](../docs/artifact-proving.md) defines the independent final theorem.  Any future detailed plan must identify the root-plan item it expands and disappear when that item completes or becomes obsolete.
