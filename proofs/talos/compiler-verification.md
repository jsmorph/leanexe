# Compiler Verification Plan

This document assesses verifying the LeanExe compiler itself and lays out a staged plan.  It complements the [CLOB verification analysis](analysis.md): that document reviews the per-artifact proofs as they stand, while this one asks what replaces them.  Nothing here is committed work; the phases below are a proposal with named decision points.

## Current Trust Position

The compiler is a Lean program with a three-stage pipeline.  `LeanExe.Extract` (about 7,400 lines) consumes the elaborated Lean environment and recognizes a supported fragment.  It produces a deep-embedded typed `IRModule` (`LeanExe.IR.Core`, about 550 lines of syntax: 46 `Expr` constructors, 7 `Cond` constructors, and about 6 statement forms) with its own evaluator in `LeanExe.Extract.Eval`.  The WASM layer then emits the binary module.

None of this is trusted today.  The proof tool regenerates the WASM from source, Talos decodes it, and a handwritten input-generic theorem relates the decoded module to the source function.  That is translation validation performed by hand, per artifact.  Its cost is the instruction-proof effort; its benefit is that the compiler changes freely, paying a regeneration and sometimes a proof repair, never a compiler-proof repair.

## Architecture of a Verified Compiler

The pipeline splits into two problems with different characters.

The back end, IR to WASM, admits a once-and-for-all theorem: for every well-formed `IRModule` m, the decoded Talos semantics of the emitted module terminates under a compiler-computed budget and returns states related to the IR evaluation of m.  Everything needed to state this exists in per-artifact form and needs generalizing: the IR evaluator promoted to a specification, one representation relation defined by recursion on `Ty` in place of the handwritten `OrdersAt`, `LevelsAt`, and `TradesAt` predicates, the refcount and ownership discipline as one preserved invariant, and allocator correctness stated per emitter template.

The front end, Lean to IR, cannot receive a once-and-for-all proof, because that would require a formal semantics of the elaborated Lean fragment.  It does not need one.  Both sides live in Lean, so the per-program statement `evalIR (extract f) = f` is directly stateable and provable by reflection as a machine-checked certificate generated at compile time.  The existing IR comparison test gate is the empirical form of this statement.  A certifying front end plus a verified back end gives end-to-end machine-checked correctness for every compiled program with no handwritten WAT proofs.

## Feasibility

The estimate is one to two person-years for the qualified claim, with three scope qualifications: the theorem anchors at the IR; the first version excludes the `memoryGrow` path and uses coarse budgets, as every artifact proof does today; and the Talos model is the semantics, with fidelity to real WASM resting on differential execution.

The grounds: the IR is small in structure, and the shared proof assets built for the artifacts are the reusable half of the job.  The mass sits in roughly 18 loop-shaped fused intrinsics (`arrayMapSlots`, `arrayFoldMultiSlot`, `arrayFilterSlots`, the append, extract, and byte-array families).  Each compiles to a loop with allocation and needs an invariant and template theorem comparable to one depth branch phase, which with the shared library is days of work each.  Scalar and control constructors are cheap.  One known wrinkle: the IR represents `nat` in 64 bits (`natAdd` evaluates as `UInt64` addition), so front-end certificates for `Nat`-using programs carry no-overflow side conditions, matching the bounded-interpretation caveat the artifact proofs already state.

## Phases

Each phase pays on its own, and the project can stop after any of them.

| Phase | Work | Gate |
|-------|------|------|
| 0 | Finish the proof-infrastructure overhaul: shared instruction-theorem library, clone consolidation, slow-module divisions, all gates green. | Aggregate proof and execution gates. |
| 1 | Promote the IR evaluator to a specification (fuel-based relational semantics or a blessed evaluation function), add a well-formedness predicate, settle the `nat` semantics. | The 62 IR comparison cases restated as Lean examples against the specification. |
| 2 | Define one `represents` relation by recursion on `Ty`, covering products, sums, structs, variants, and recursive variants; state the ownership discipline as one invariant.  The recursive case builds on the `RelTree` ownership-tree work. | Prove `OrdersAt`, `LevelsAt`, and `TradesAt` equivalent to instances of the generic relation. |
| 3 | Restate the shared theorems over IR constructors: allocator, copy loops, folds, searches, and the calling convention through `TerminatesWith`; one emitter template per constructor, scalars first, loop intrinsics in dependency order. | Focused warning-failing build per template. |
| 4 | The back-end theorem: structural induction over `Expr` and `Stmt` gluing the templates, with a module-level budget function.  Module division discipline applies from the first file, because the elaboration cost of the induction is the known engineering hazard. | Focused build of the induction modules; the theorem statement reviewed against the scope qualifications. |
| 5 | Front-end certificates: compile-time generation of `evalIR (extract f) = f` by reflection, wired into the Talos tools as a third gate, with a recorded fallback to differential testing where kernel reduction is too slow. | Certificates for all twenty registered cases. |
| 6 | Re-derive the twenty artifact theorems from the compiler theorem plus their source-property modules; retire the per-artifact instruction proofs. | Aggregate gate over the re-derived theorems. |

## Decision Points

Four decisions belong to the project owner before or during the work: whether the `memoryGrow` path enters the first version (this plan defers it); budget precision (coarse first, sharpened only if a consumer needs it); the `Nat` overflow policy for certificates; and whether `Extract`'s fragment recognizer ever receives certificates or stays gated by differential tests.

## Implications and Costs

What the theorem buys: artifact proofs collapse to source-level reasoning plus a certificate, and each new export costs a source-property module instead of weeks of instruction proofs.  What it does not buy: the Lean elaborator and kernel remain trusted; Talos-model fidelity and host ABI conformance remain empirical; resource behavior and performance of generated code are untouched.

Two costs arrive with success.  The compiler ossifies: every emitter change reopens phase 3 or 4, and the current freedom to change the compiler against regeneration gates disappears.  Review concentrates: today a mistake in one artifact's predicates is contained to that artifact, while a mistake in the one generic representation relation would weaken every artifact claim at once.  The defensible claim after phase 6 is exactly: for every well-formed IR module, the emitted code's decoded Talos semantics terminates under the stated budget and returns states related to IR evaluation, and for each compiled program a reflection certificate ties the IR to the source function.
