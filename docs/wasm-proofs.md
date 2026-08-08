# Reusable WASM Proof Library Plan

This plan establishes a curated Lean library for proving behavioral properties of exact WebAssembly artifacts.  It builds on the shared arithmetic, memory, weakest-precondition, runtime, and portability results already used by the Talos artifact proofs.  It also defines how a headless proof agent such as Pi discovers and applies that library while iterating with Lean.

## Goal and boundaries

The library should reduce repeated proof engineering without changing the subject of verification.  A generated theorem must continue to concern the module decoded and validated from exact WASM bytes under the pinned Talos semantics.  Shared lemmas may describe those semantics, generated instruction patterns, the LeanExe runtime representation, or mathematical facts independent of the source program.

The library dependency closure must exclude the generated Lean Source module, the LeanExe compiler, compiler IR, and source-to-WASM claims.  A proof agent may receive the frozen formal specification, WAT-derived execution model, exact-artifact support, and curated proof library.  Independent verification must audit that closure and pin every retained library source that contributes to the theorem.

Automation should handle mechanical obligations whose meaning is stable across artifacts.  Suitable work includes instruction stepping, local-frame access, address normalization, read-over-write chains, fixed-width arithmetic normalization, and standard loop-rule setup.  Allocation meaning, ownership, source-level data representation, and application behavior should remain explicit named theorems whose premises and conclusions a reviewer can inspect.

## Existing proof base

The repository already contains a substantial reusable layer.  More than forty artifact modules directly import one of the shared common, scaffold, runtime, or function-region families.  The [proof-engineering notes](plan-notes.md) record additional reusable assets, example consumers, failed approaches, and measured elaboration boundaries.

| Area | Current source | Reusable content |
|------|----------------|------------------|
| Arithmetic and basic memory | [`Project.Common`](../proofs/talos/lean/Project/Common.lean) | `UInt64` and `UInt32` normalization, `u64_omega`, optional-list access, byte predicates, read/write framing, `read_frames`, guarded branches, and `wp_run_with`. |
| Control flow and folded frames | [`Project.WpScaffold`](../proofs/talos/lean/Project/WpScaffold.lean) and [`Project.FrameAttr`](../proofs/talos/lean/Project/FrameAttr.lean) | Generic loop-body introduction, folded-frame stepping, byte framing, and mixed byte/word read normalization. |
| Runtime semantics | [Runtime specifications](../proofs/talos/lean/Project/Runtime/Spec.lean), [free-list model](../proofs/talos/lean/Project/Runtime/FreeList.lean), and [ownership-tree proof](../proofs/talos/lean/Project/Runtime/TreeSpec.lean) | Retain and release theorems, fixed-array release, free-list selection and unlinking, recursive ownership trees, counters, memory framing, and allocation arithmetic. |
| Function transport | [Function-region syntax](../proofs/talos/lean/Project/FunctionRegion/Syntax.lean) and [execution transport](../proofs/talos/lean/Project/FunctionRegion/Exec.lean) | Instruction-region execution, function-index renaming, portable calls, and transport of termination results between compatible modules. |
| Representation and allocation patterns | [`Project.Clob`](../proofs/talos/lean/Project/Clob.lean), fixed-array allocation modules, and completed CLOB proofs | Fixed-array headers, capacity arithmetic, owned representations, allocation branches, copy invariants, and store frames with a mixture of general and application-specific statements. |

The first `leanexegen` proof task could not use most of this material.  Its import validator permitted generated modules, `CodeLib`, `Interpreter`, `Mathlib`, `Std`, and `Init`, while rejecting `Project.Common`, `Project.WpScaffold`, and the runtime modules.  The current proof kit admits audited memory, `Array UInt64`, and control-flow modules and gives Codex their checked catalog in every proof task.

## Library design

### Modules and dependency control

The first implementation phase should create a stable proof-library facade without moving established theorems.  The plan uses `WasmProof` as a provisional namespace, with final naming resolved before files or public imports move.  Facade modules can initially import and re-export the checked declarations from their present locations, allowing proof consumers to adopt stable imports while existing artifact proofs remain unchanged.

| Proposed module | Initial contents | Import restriction |
|-----------------|------------------|--------------------|
| `WasmProof.Arithmetic` | Fixed-width normalization, no-wrap conversions, list access, and bounded arithmetic tactics. | Lean core, Mathlib arithmetic, and neutral proof attributes. |
| `WasmProof.Memory` | Byte and word reads and writes, `BytesAt`, framing, disjointness, and read-over-write tactics. | Talos memory semantics and `WasmProof.Arithmetic`. |
| `WasmProof.Control` | Weakest-precondition entry, calls, branches, loops, folded local frames, and generated-frame attributes. | Talos weakest-precondition semantics, arithmetic, and memory support. |
| `WasmProof.Runtime` | Allocator, retain, release, free-list, fixed-array, ownership-tree, counter, and runtime-frame theorems. | Curated runtime definitions plus the three lower layers. |
| `WasmProof.Portability` | Function-region equality, renaming, call transport, and termination transport. | Talos execution semantics without artifact-specific programs. |

Each facade module needs an audited transitive import closure.  The audit should reject generated Source modules, compiler modules, case-specific `Program` modules, and umbrella imports that bring complete artifact specifications into the library.  `leanexegen` should allow only the curated namespace rather than the complete `Project` namespace, and its package validator should repeat the closure audit during independent verification.

The proof package must identify the library revision or content digest.  Verifier-source identity should include every facade and implementation file reachable from a generated proof.  A changed lemma, tactic, simp attribute, or transitive dependency must invalidate stale proof evidence and require the package to rebuild under the new identity.

### Distillation policy

A shared declaration should have two independent consumers before promotion unless it states a direct theorem about the pinned Talos semantics.  The two consumers must use the same semantic statement rather than share only similar generated syntax.  The asset catalog should name those consumers and state whether reuse is direct, requires an adapter, or supplies only a proof pattern.

Theorems should carry semantic content, while tactics should normalize routine syntax.  A fixed-array allocator theorem should state the resulting header, ownership, globals, pages, and frame conditions.  A tactic may discharge the repeated local-index reductions or read-over-write steps needed to apply that theorem, but it should not infer or hide ownership and allocation premises.

Case-specific mathematics and generated layouts should remain local.  In the prime-factor proof, the factorization lemmas belong with the formal specification, while the exact `factorFrame`, local indices, and loop invariant belong with that artifact.  The generic weakest-precondition opening, loop-body scaffold, fixed-width arithmetic, and frame normalization belong in the shared library.  The table records the default review action for each repeated pattern.

| Repeated material | Default action |
|-------------------|----------------|
| A theorem already consumed by two artifacts | Move behind the stable facade, add it to the checked catalog, and retain both consumers as tests. |
| The same mechanical rewrite sequence in two artifacts | Add a narrowly scoped tactic or simp attribute with explicit inputs and a focused test. |
| Similar generated code with different semantic postconditions | Retain separate adapters and share only the lower semantic theorem. |
| One expensive artifact-local proof | Divide its theorem boundary first; generalize only after another consumer confirms the statement. |
| Domain mathematics used by one specification | Keep it in a specification or case-specific mathematical module. |

### Pi discovery and use

Pi's knowledge of the library should come from checked task inputs rather than model memory.  Each proof workspace should contain a compact `PROOF_LIBRARY.md` catalog that names the available module, declaration, exact purpose, important premises, and representative consumers.  A Lean catalog module should contain `#check` statements for every advertised declaration so the readable catalog cannot retain a stale name or signature unnoticed.

Leanexegen now classifies the export-reachable functions in the frozen Talos `Program` before starting Codex.  It records calls, instruction and local counts, loops, memory operations, arithmetic, and allocation features in `PROOF_TASK_FEATURES.json`, then selects matching marked sections from the [artifact-proof strategy notes](proof-strategies.md) into `PROOF_STRATEGIES.md`.  The initial selector handles the fixed array ABI and the current generated instruction shapes; retain, release, recursive ownership, and function-index transport still need classifiers when generated examples require them.

Codex should inspect the catalog and generated model, import the smallest suitable facade modules, and use `#check` or `#print` in its workspace before applying an unfamiliar theorem.  Its existing iterative session should continue to run the prescribed Lean target after edits.  The outer orchestrator should repeat the final build, import audit, axiom audit, and artifact check without trusting Codex's report.

The prompt should state the proof-library boundary directly.  It should permit the curated namespace, prohibit arbitrary `Project` imports, and name the catalog file and feature classification.  It should also explain that completed artifacts are examples rather than authorities: every imported theorem must pass Lean, and every case-specific adaptation remains part of the generated proof.

### Control-flow tactic PoC

The 2026-08-03 PoC adds a [control-flow tactic module](../proofs/talos/lean/Project/ProofKit/Control.lean) and a compact [proof-kit catalog](../proofs/talos/lean/Project/ProofKit/README.md).  Its `wp_entry functionDef as initial'` tactic applies `Wasm.TerminatesWith.of_wp_entry`, closes the generated-function lookup with `rfl`, and names the initial local frame.  The tactic replaces a repeated three-line opening while leaving the complete function-body weakest-precondition goal and all later proof steps visible.

The test workspace copied the demo proof modules into `/tmp`, omitted `Source.lean`, and depended on the repository proof project for the new module.  The headless invocation selected Pi's existing `openai-codex` login; Pi then read the copied catalog, added the proof-kit import, and used the tactic at both entry sites in the prime-factor proof.  A diff against the [generated behavior proof](../demos/demo-1/proof.lean) contains one import and the two intended replacements; every theorem and later proof step remains unchanged.

The follow-up tactic `wp_entry_single_call functionDef unfolding functionBody as initial' using callProof` handles a common generated wrapper shape.  It enters and unfolds the wrapper, symbolically executes to one direct call, applies the explicit `Wasm.wp_call_tw` theorem, and executes the return continuation.  The [retained refactoring](../demos/demo-1/proof-kit.diff) reduces the public prime-factor artifact theorem from nine mechanical proof commands to one tactic invocation while retaining `helper_correct` as its semantic argument.

Pi's prescribed entry-tactic build and separate outer builds of both refactorings completed the exact `LeanExeGen.GeneratedRc8c2d9f87deb0758.ArtifactResult` target.  The single-call version built the changed behavior module in 11 seconds and its artifact result in 1.6 seconds on Lean 4.31.0, with the demo proof's existing linter warnings.  `leanexegen` now permits only the named proof-kit module, supplies the catalog to Codex, records both files in the package identity, audits the imported module, and compares the packaged catalog during independent verification.

A from-scratch `leanexegen` run then generated the same WASM artifact as the retained baseline and used both cataloged tactics.  The behavior proof fell from 329 to 321 lines, and the independent verifier accepted the packaged artifact theorem.  Stage five took 253.925 seconds, compared with 238.557 seconds in the baseline, so the run demonstrates discovery and proof reduction but supplies no evidence of faster generation; the [retained process streams](../demos/demo-1/README.md#live-proof-kit-generation) record the measurement.

The structural loop follow-up adds `wp_block_loop invariant inv decreasing measure` for the common Talos block/loop rule pair and `wp_entry_to_loop functionDef unfolding functionBody as initial'` for a generated entry that symbolically executes to that loop boundary.  Both tactics accept only control-flow structure, and the proof supplies its application invariant, decreasing measure, initialization, preservation, decrease, and exit arguments.  Focused builds applied each tactic separately to the retained 1,348-byte prime-factor artifact theorem and completed `ArtifactResult` under Lean 4.31.0.

The `leanexegen reprove` mode then regenerated only `Behavior` from the retained package with the new catalog.  The command preserved the specification, Source, WASM, Program, and deterministic artifact modules byte-for-byte, and Codex used `wp_entry_to_loop` and `wp_entry_single_call` in the accepted 316-line proof, five lines shorter than the prior 321-line proof.  Controlled stage five took 390.849 seconds, compared with 253.925 seconds for the previous proof-kit run, so the abstraction reduced proof text without reducing elapsed proof-stage time.

## Work plan

| Phase | Work | Acceptance gate |
|-------|------|-----------------|
| 0. Baseline inventory | Record the current shared declarations, direct consumers, build times, import closures, and artifact-local candidates.  Reconcile this inventory with the proof-engineering notes. | Every promoted candidate names its source, signature, first two consumers, and current focused build result. |
| 1. Stable facade | Select the public namespace and add arithmetic, memory, control, runtime, and portability facade modules without moving theorem bodies. | Each facade builds through `tools/leanrun`; existing aggregate proofs remain unchanged and pass their normal gate. |
| 2. Dependency enforcement | Add an exact proof-library allowlist, transitive closure audit, source and compiler exclusions, and library identity to proof-package pins. | Tests accept every curated facade, reject arbitrary `Project` and Source imports, reject a forbidden transitive dependency, and invalidate a changed library digest. |
| 3. Checked catalog | Write the declaration catalog, its Lean `#check` companion, feature tags, premises, and representative consumers. | The catalog target builds, every local link resolves, and removing or renaming an advertised declaration fails the check. |
| 4. Codex integration | Add the catalog and artifact feature summary to the isolated proof workspace and revise the proof prompt to use them. | A mocked task receives the expected files and permissions, while the final proof context still contains no Source module or compiler. |
| 5. Scalar-loop pilot | Repeat the prime-factor artifact proof with the proof library available.  Record which declarations Codex inspected and used, its Lean iterations, and the outer verification time. | Codex produces the same `ArtifactSpec` theorem for the exact retained bytes, imports at least one curated module, and passes independent verification. |
| 6. Memory-runtime pilot | Select one completed allocation or release artifact and exercise the memory, runtime, and framing layers through Codex. | The proof reuses a semantic runtime theorem and a mechanical framing tactic, preserves its existing statement, and passes focused and aggregate artifact checks. |
| 7. Distillation cycle | Review each later proof and its retained journal for repeated semantics, agent-created local adapters, failed proof strategies, expensive boundaries, and missing catalog entries. | A promoted declaration explains the journal evidence that motivated it, satisfies the two-consumer rule, has a focused test, updates the catalog, and does not regress measured consumers beyond an explained bound. |

Phase 1 should avoid theorem migration because a facade provides value with less proof churn.  Phase 2 precedes agent access so a prompt change cannot widen the dependency boundary before the verifier enforces it.  The two pilots then test different parts of the library: the scalar-loop pilot tests discovery and control flow, while the memory-runtime pilot tests semantic reuse and framing automation.

Each successful generated proof now retains a prose journal beside its checked source and timing telemetry.  The distillation review compares those three records: the journal explains the agent's choices, the source reveals local abstractions and repeated proof terms, and telemetry measures the complete result.  Later runs test whether a promoted LTG declaration appears in the next journal and accepted proof before timing comparisons influence retention.

## Validation and completion

Focused Lean checks must run through `tools/leanrun` under the repository resource policy, and proof targets must remain serial.  JavaScript tests should cover import classification, transitive dependency rejection, catalog routing, feature selection, task-context contents, prompt contents, package identity, and verifier rejection of stale library pins.  The artifact gate should rebuild both pilots and the aggregate proof library after every promoted theorem or tactic.

Performance evidence should report complete proving time as the primary metric and accepted proof structure as secondary evidence.  Each promoted tactic or scaffold needs before-and-after times and a comparison of proof lines, syntax volume, local scaffolding, and shared theorem use for its first two consumers; raw source bytes and identifier length do not measure proof complexity.  A timeout without a diagnostic requires a smaller module or theorem boundary before another unchanged run, following the repository proof policy.

The plan is complete when a Codex proof session can discover and import the curated library, use it in both scalar-control and memory-runtime proofs, and produce packages that verify independently without Source or compiler access.  The checked catalog, import closure, and content identity must prevent undocumented or stale dependencies.  Continued distillation then becomes routine maintenance governed by the two-consumer rule rather than a separate proof-library project.

## Relationship to verification plans

The [artifact-level verification plan](../plans/artifact-verification.md) supplies the exact-byte, decoder, validator, translation, and behavioral-theorem boundary consumed here.  This library plan improves construction of the behavioral theorem without introducing a source theorem or compiler-correctness premise.  The artifact verifier remains useful when no source program exists.

The [source-theorem transport plan](../plans/theorem-transport.md) may later use the same arithmetic, memory, control, and runtime support.  Its lowering and refinement theorems have a different subject and dependency boundary, so they should not enter the artifact proof library by default.  A theorem useful to both plans belongs in a neutral module only after its import closure and statement support both uses.
