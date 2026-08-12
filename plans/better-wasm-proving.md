# Plan for Better Direct WASM Proof Generation

| Field | Value |
|---|---|
| Status | Reference roadmap and experiment record.  Later annotation, structured-LTG, and composition work supersedes parts of the unchecked queue. |
| Date | 2026-08-05; evaluation policy revised 2026-08-09 |
| Correctness gates | Accepted artifact theorem and independent package verification |
| Evaluation dimensions | LTG retrieval, agent revisions, proof structure and size, shared abstraction use, compiler-derived evidence use, applicability, and Stage 5 time |
| Fixed artifact | SHA-256 `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7` |
| Retained baseline | `.lake/leanexegen-runs/demo1-timing-1` |
| First faster result | `.lake/leanexegen-runs/demo1-timing-2` |

Accepted artifact theorems and independent package verification are mandatory gates.  Each accepted iteration receives a scorecard covering LTG search and selection, agent revisions, proof structure and size, shared theorem or tactic use, compiler-derived evidence use, applicability beyond the measured program, and Stage 5 time.  No single scorecard dimension determines retention or promotion.  Line count, explicit syntax, local scaffolding, repeated derivations, and shared theorem use describe proof complexity; raw byte count, word length, and identifier length do not.  A long declaration name can indicate that the proof reused a checked abstraction instead of rebuilding its argument.

The [technical analysis](../docs/better-wasm-proving.md) describes the available mechanisms and their logical boundaries.  This plan begins with measurement and complete semantic regions rather than additional leaf arithmetic because those changes affect several scorecard dimensions.  Every controlled comparison must concern the same frozen formal specification, `Program`, WASM, Codex identity, model settings, toolchain, machine profile, and cache policy.

## Evidence and target

The retained timing-1 package took 3,516.775 seconds in stage 5.  The controlled timing-2 reproof changed only the proof kit and guidance, used the same WASM bytes, and took 1,964.130 seconds.  The 1,552.645-second reduction equals 44.15 percent, although one run does not establish a stable distribution.

Timing-1 produced a 579-line proof, while the faster timing-2 run produced 591 lines.  This result shows that proof time and proof size can move in different directions, so every comparison must report both.  The immediate task is to reproduce the timing reduction, then replace complete discovery and execution regions so later phases can improve one metric without concealing a regression in the other.

The unchanged word-address series took 1,964.130, 360.144, and 2,249.443 seconds, for a median of 1,964.130 seconds and a range of 1,889.300 seconds.  Three proofs using `Project.ProofKit.FixedArrayAllocator.region_spec` took 2,556.812, 1,134.008, and 941.494 seconds.  Their 1,134.008-second median passes the 1,758-second semantic-workbench gate and is 42.3 percent below the word-address median.

Three proofs using `Project.ProofKit.FixedArraySingleton.region_result_spec` took 680.396, 436.403, and 489.993 seconds.  Their 489.993-second median is 56.8 percent below the allocator median and 75.1 percent below the word-address median.  The demo-1 result passes the longer 900-second target through a checked runtime-region theorem, while the plan still requires application to demo-2.

## Invariants

The final artifact-only theorem must continue to mention the exact Talos module derived from the embedded WASM bytes.  Proof generators, source proofs, compiler traces, structural maps, retrieval tools, and language models may propose evidence.  Lean must check every retained target claim against the exact `Program` and the existing decoded-byte equality.

The artifact-only proof closure may contain `FormalSpec`, neutral mathematics, a source-free semantic capsule, the exact `Program`, checked structural declarations, proof-kit modules, target certificates, and artifact-support modules.  It must exclude Source, source theorem declarations, compiler IR, extraction declarations, emitter declarations, compiler traces, and lowering theorems.  Direct composition with a source theorem and checked lowering remains the separate theorem-transport result described in [Theorem Transport](theorem-transport.md).

Each machine serializes Lean commands through its own runner and semaphore.  One local Lean command and one `dev` Lean command may run concurrently because the locks and cgroups belong to separate machines.  Timing comparisons must remain on one fixed lane because the local and remote architectures, CPU quotas, memory limits, and caches differ.

## Work streams

| Stream | Main result | Dependencies | Lean lane |
|---|---|---|---|
| Measurement | Fixed benchmark fixture and stage-5 telemetry | Current packages | Local benchmark lane |
| Artifact workbench | Exact proof map, checked regions, split proof modules, retrieval | Map schema after measurement starts | `dev` for checks, local for benchmarks |
| Runtime semantics | Empty-search bump allocator and array-wrapper theorems | Existing Talos runtime proofs | Local or `dev` |
| Source assistance | Ideal hints, typed annotations, semantic capsule | Source proof and boundary audit | `dev` for capsule checks |
| Target automation | Proof-producing VCG and optional target normalization | Checked region API | Local or `dev` |
| Theorem transport | Source-to-IR certificate and verified lowering | Existing transport plan | Separate result and package |

The measurement stream owns `tools/leanexegen` and `tools/leanexegen-lib.js` while telemetry and package schemas change.  The artifact-workbench stream owns new `Project.ProofWorkbench` modules and generated structural files.  Runtime and source-assistance streams use new modules so they can proceed without overlapping orchestration edits.

## Compiler theorems for WAT proof generation

Compiler theorems can reduce WAT proof work without entering the retained artifact theorem.  The compiler proves that a supported IR fragment emits a canonical neutral descriptor, while the artifact package independently proves that the descriptor program equals an exact interval of the decoded Talos `Program`.  The artifact proof then applies semantics proved for the neutral descriptor, retaining its independence from Source, extraction, compiler IR, and emitter declarations.

The [compiler-theorem analysis](../docs/compiler-theorem-bridge.md) defines the first restricted theorem boundary and records the current compiler inventory.  Its scalar reification increment now covers Demo 1's guard and complete loop body, proves production emission agreement, emits versioned descriptor data, and generates an exact decoded-region equality.  The remaining experiments add semantic information only when a neutral artifact-side checker or theorem can verify the same information against the descriptor and exact WAT-derived program.

| Experiment | Compiler theorem or analysis | Artifact-side result | Proof work removed | Acceptance test |
|---|---|---|---|---|
| Scalar emission | Successful IR reification emits the descriptor program | Exact region equality and `ScalarTransition.whileProgram_spec` | Instruction decoding, checked division expansion, branch shape, assignment order, and scratch handling | Isolated screen was 47.202 percent slower, with 6.648 percent fewer lines and 4.710 percent fewer words |
| Effects and frames | Descriptor reads, writes, and scratch interval bound all local changes | Recomputed frame certificate and preservation lemmas | Local-frame reconstruction and unchanged-local proofs | Mutation rejection plus evidence of reuse, fewer revisions, simpler proof structure, or lower time |
| One-step semantics | IR evaluation agrees with descriptor evaluation for one loop step | Closed transition equations over the fixed local frame that summarize scratch staging | Descriptor evaluation, branch update algebra, scratch-state equality, and local-numbering discovery | Scorecard improvement on Demo 1 and a held-out scalar loop |
| Annotation locations | Annotated composition preserves path and interval coordinates | Exact coverage and non-overlap certificate | Region navigation, decomposition, and continuation reconstruction | Every coordinate mutation fails before behavior proving |
| Cut-point graph | Emitted fragments compose into loop-head, call, allocation, and return transitions | Checked graph over exact decoded regions | Control-flow discovery and repeated composition scripts | Proof obligations contain application predicates rather than instruction lists |
| Range facts | Abstract interpretation proves intervals, nonzero divisors, and representation bounds | Neutral checker validates each fact over descriptor transfer | Repeated fixed-width normalization and range searches | Useful checked facts appear in two structurally different artifact proofs, with time recorded |
| Source-proof projection | Proven source relations map to IR slots and cut points | Candidate invariant or source-free semantic capsule rechecked over the descriptor | Invariant discovery and mathematical lemma selection | Artifact closure excludes compiler declarations and the scorecard records whether projection reduced discovery work |

The experiments proceed in table order because each row supplies evidence and theorem structure needed by the next.  A compiler-side proof alone does not qualify an experiment: exact decoded-region agreement, compiler-free artifact closure, emitter byte compatibility, and independent package verification remain required.  Timing comparisons use complete Stage 5 duration under one Codex version, reasoning level, machine profile, cache policy, formal specification, and WASM artifact.

The first fixed-artifact annotated trial increased Demo 1 Stage 5 from 2,017.931 to 3,692.913 seconds.  A later isolated comparison retained the same direct-call recipes and changed only the scalar-loop region: the calls-only control took 2,645.818 seconds, while the scalar candidate took 3,894.697 seconds.  The candidate used the generated descriptor equality and loop theorem, reduced accepted source from 722 to 674 lines and from 3,418 to 3,257 whitespace-delimited words, and failed the proving-time screen despite that structural reduction.

The matched journals show that the control reconstructed the neutral descriptor early, after which both agents faced the same semantic invariant and fixed-width arithmetic.  The candidate also spent substantial time aligning the public singleton wrapper and allocator theorem, so the later compact-transition comparison used a shared wrapper composition in both configurations.  Checked fixed-frame transition equations summarize intermediate scratch staging because the raw descriptor exposed evaluator and local-state details that dominated the residual scalar proof.

The compact transition increment passes its matched Demo 1 screen.  `ScalarTransitionU64` proves generic correspondence with the typed evaluator, while generated annotation support states the complete condition and body transitions over a fixed `UInt64` frame.  The control retained length dispatch, mandatory calls, and the complete singleton wrapper but omitted the scalar-loop region; the candidate added only that region, and independent package verification accepted both.

The control completed Stage 5 in 2,262.084 seconds, while the candidate completed in 1,965.454 seconds.  The transition equations reduced total proving time by 296.630 seconds, or 13.113 percent, and Codex-session time by 323.088 seconds, or 14.945 percent.  The candidate used three condition-equation rewrites and five body-equation rewrites, reduced `wp_run` applications from 36 to 12, and reduced accepted source from 643 to 635 lines.

The journals identify function-entry normalization as the next general boundary.  Both agents spent checks establishing argument order, fixed-store quantification, and the exact local frame at the loop head, while the candidate also needed to align that frame with generated `U64State`.  A checked entry-to-loop adapter should remove this work before the compact transition method reaches a held-out scalar artifact.

- [x] Reify Demo 1's scalar IR into a neutral descriptor and prove production emission agreement.
- [x] Generate and Lean-check exact descriptor equality against Demo 1's decoded WAT region.
- [x] Preserve Demo 1's frozen WASM bytes and pass execution, serializer, and aggregate Talos gates.
- [x] Record and preserve a matched Codex-version calls-only control and isolated scalar-descriptor screen.
- [x] Reject repeat scalar-descriptor trials after the isolated screen regressed proving time.
- [x] Add descriptor effect sets and generic artifact-side frame theorems.
- [x] Generate closed one-step transition equations and verify them against Demo 1's exact artifact.
- [x] Test whether Codex uses the transition equations and measure the matched Stage 5 result.
- [x] Generate a checked function-entry-to-scalar-loop adapter and screen it on fixed Demo 1.
- [x] Freeze a held-out scalar-loop demo before exposing descriptor data.
- [x] Add and screen checked annotation-location composition after the semantic rows pass their timing gates.
- [ ] Pilot a checked cut-point graph on two artifacts with different control-flow structure.

## 2026-08-09 continuation

Structured LTG retrieval is now the canonical proof-library interface.  A proof task starts from the category index, searches bounded JSONL summaries, opens selected canonical entries, and records its searches and decisions in the journal.  Each experiment must review that retrieval record with the accepted proof and telemetry, then update catalog aliases, entry relationships, theorem support, annotations, or journal instructions when the evidence identifies a defect.

Demo 9 introduces a bounded wrapping sum over `Array UInt64`.  It exercises an input-traversal fold, a loop-carried accumulator, singleton-result allocation, and the compiler's existing `leanexe.loop.fold.v1` annotation.  The current artifact-side recipe checks the fold's control skeleton but supplies only generic block and loop rules, making this demo the first test of semantic fold annotations and fold-oriented LTG.

The first Demo 9 run freezes the specification, source, WASM, decoded Program, annotations, journal, and telemetry before any fold-specific support enters LTG.  The journal determines whether the next increment should reify the element load and accumulator transition, prove an exact neutral fold-program equality, add a reusable traversal theorem, or improve retrieval and guidance.  A controlled reproof then keeps the artifact fixed and compares proof acceptance, retrieval, revisions, proof structure and size, shared abstraction use, compiler-derived evidence use, applicability, and time.

Further demos should separate development cases from nearby and distant held-out cases.  A second reduction with a different accumulator layout can test whether fold support generalizes without changing the array traversal, while a later demo should exercise a missing control or memory motif rather than another reduction.  The compiler acceptance report and the preceding journals determine the exact program shapes before each request freezes.

## Phase 0: Preserve the case and measure the process

The timing packages should be copied from `.lake` into a checked benchmark fixture before cache cleanup or another reboot can remove them.  The fixture is small enough to retain both timing-1 and timing-2, their exact WASM, and a benchmark manifest.  The manifest must record every identity that can invalidate a timing comparison.

Proposed paths are `benchmarks/leanexegen/demo1-array/timing-1`, `benchmarks/leanexegen/demo1-array/timing-2`, and `benchmarks/leanexegen/demo1-array/benchmark.json`.  A new `tools/leanexegen-benchmark` command should reject a comparison when any frozen module, artifact byte, model setting, tool pin, resource profile, or declared cache policy differs.  The command should run `reprove`, require successful publication, and invoke independent verification as a gate after timing has stopped.

Telemetry should identify which changes lower proof time.  It should record the Codex session interval, candidate hashes and write times, Lean command targets and durations, diagnostics, timeouts, and the outer acceptance interval.  Complete model conversations and large terminal transcripts need not enter the package.

- [x] Copy the seven retained timing packages into the checked benchmark fixture.
- [x] Add benchmark identity validation and a declared warm-cache policy.
- [ ] Record `codex exec --json` command events when the protocol supplies stable identifiers.
- [ ] Add a traced `tools/leanrun` fallback if Codex events cannot identify Lean commands reliably.
- [ ] Extend stage reports with per-command timing while retaining schema-1 verification.
- [x] Run two more unchanged timing-2 reproofs and compute the three-run median and range.

The benchmark driver rejects a mutated frozen input, validates all seven retained proof packages, and reports variant medians and ranges.  Telemetry distinguishes Codex-session time from outer-acceptance time, while individual Lean-command timing remains open.  Failure to collect telemetry may invalidate a benchmark record, but it must not invalidate an otherwise checked artifact package.

## Phase 1: Build an artifact-derived proof workbench

The current feature extractor gives Codex function counts and nearly every strategy section.  It does not identify exact calls, structured paths, local meanings, runtime templates, or theorem applications.  A checked artifact map should compute those facts once before proof generation.

`Project.ProofWorkbench.ProgramMap` should traverse the imported `Wasm.Module` and report reachable functions, structured instruction paths, calls, local types, loads, stores, globals, branch targets, simple address producers, and region fingerprints.  A generated `ProofMapDump.lean` imports the exact case `Program`, and `tools/leanexegen-proof-map.js` serializes and validates the result.  Runtime recognizers must report the first differing instruction when a template does not match.

The same map should generate `ProofStructure.lean`.  That module defines named regions, proves function decompositions, generates folded local frames and `frame_step` facts, and proves exact equality between recognized regions and canonical proof-kit templates.  Every structural equality must close through `rfl` or another small checked list theorem.

Demo-1 should split into `Behavior.Math`, `Behavior.Func0`, `Behavior.Func1`, `Behavior.Entry`, and a short `Behavior` composition module.  Leanexegen should run one focused Codex task per unit and retain every accepted module before starting the next.  Editing `Entry` must use the cached `Func0` and `Func1` oleans rather than elaborating their source again.

- [ ] Add the exact `ProgramMap` traversal and JSON schema.
- [ ] Recognize demo-1's scalar loop, conditional scalar wrapper, singleton ABI branch, empty free-list search, bump allocator, and result stores.
- [ ] Generate exact region declarations and decomposition theorems.
- [ ] Generalize frame-lemma generation from the mapped parameter and local types.
- [ ] Expose folded-frame support through an audited `Project.ProofKit.Frame` module.
- [ ] Generate split proof units and record a stage report for each unit.
- [ ] Resume an interrupted proof at the first incomplete unit without regenerating accepted units.

Phase 1 passes when a one-instruction mutation rejects the old structural module, a focused `Entry` edit does not rebuild `Func0`, and three fixed reproofs establish the scorecard effects of the split.  If additional Codex sessions cost more time than module checkpoints save, that cost weighs against the gains in checkpointing, proof structure, and diagnostic isolation.  Adjacent units may merge while their checked interfaces remain when the combined evidence favors that form.

## Phase 2: Replace complete runtime regions

`Project.ProofKit.FixedArrayAllocator.region_spec` now covers the inlined empty-free-list search, bump allocation, page decision, six header stores, allocator-counter update, and returned array root.  The theorem has no CLOB dependency and parameterizes the fixed-array capacity and stride.  An exact demo-1 check identifies the emitted instruction slice with `FixedArrayAllocator.region 1` and instantiates the theorem against the frozen `Program`.

`Project.ProofKit.FixedArrayRuntime` should define the canonical program template.  `Project.ProofKit.AllocationRegion` should contain readiness and result records plus a continuation-style `wp_empty_search_bump` theorem.  The generated structural module should prove that the concrete demo region equals the canonical template before the artifact proof applies the semantic theorem.

The following theorem should cover the complete singleton-array ABI wrapper.  It accepts an input representation, scalar callee summary, allocator readiness, and an equation connecting the scalar result to the expected singleton element.  Its conclusion handles both the unchanged non-singleton branch and the newly allocated singleton branch.

- [x] Distill the neutral empty-search bump theorem from the established runtime proofs.
- [ ] Bundle memory, global, page, pointer, frame, and representation premises into small records.
- [ ] Add a checked adapter for the existing CLOB consumer.
- [x] Apply the theorem to demo-1 through an exact region equality.
- [x] Add the parameterized singleton allocator-and-result-region theorem and demo-1 adapter.
- [x] Add a complete public singleton-wrapper theorem parameterized by a scalar callee summary.
- [ ] Use demo-2 as the second consumer before declaring the wrapper API stable.

The Demo 1 allocator-and-result-region timing and proof-coverage gates have passed.  `FixedArraySingletonWrapper.wrapperProgram_spec` now covers the public length dispatch, checked element load, scalar call, capacity calculation, allocator, result stores, and public return while accepting a store-preserving scalar callee summary.  The annotation consumer recognizes Demo 1's exact entry shape, generates a whole-function equality checked by `rfl`, selects the complete theorem, and starts the proof at that wrapper boundary.

`tools/leanexegen annotate` reproduced the 1,938-byte Demo 1 artifact and built the generated whole-function equality.  The protocol test rejects a changed result-local assignment, and the focused proof-kit build accepts the generic theorem under Lean 4.31.0.  Demo 2 remains the required second consumer before treating the complete wrapper interface as stable, while a fixed-artifact timing screen must determine whether the wrapper removes the journaled entry-proof cost.

## Phase 3: Supply exact proof-library selections

The current task receives about 31 KB of catalog and strategy prose, and demo-1 selects every strategy section.  A proof agent needs exact declarations and examples for its current checked region.  More general prose will increase selection work without establishing a target fact.

A machine-readable catalog should record declaration names, signatures, modules, structural tags, premises, compatible fingerprints, and one checked application.  A `CatalogCheck.lean` module should check every advertised declaration and example.  `tools/leanexegen-proof-query.js` should select the smallest useful set from the current proof unit and exact region map.

- [ ] Define and check the catalog schema.
- [ ] Index the current proof-kit modules and semantic runtime theorems.
- [ ] Generate `PROOF_GOAL.json` and `PROOF_SELECTION.json` per proof unit.
- [ ] Rank the relevant theorem among the first three results for every demo-1 unit.
- [ ] Exclude unrelated retain, release, CLOB, LEB128, and copy guidance from demo-1 tasks.

Phase 3 passes only when the selected context reduces median stage-5 time.  A retrieval miss may fall back to the full checked catalog, but telemetry must record the miss.  Context size serves as an explanatory measure rather than an acceptance measure.

The first context-only screen failed this gate on held-out Demo 7.  A checked-recipe selector reduced the combined prompt and supplied guidance from about 13,500 words to about 6,800 words, and both agents used the selected modules without a fallback, but two runs took 777.102 and 818.470 seconds.  Even an arbitrarily fast third run would leave a 777.102-second median, 49.2 percent above the retained 520.815-second median, so the selector was removed and its packages were preserved.

The journals place the remaining cost in invariant construction, compact-state normalization, and repeated complete Lean checks rather than proof-library discovery.  Another Phase 3 attempt therefore depends on a smaller proof unit, a checked skeleton, or a goal-indexed declaration query that changes the proof work performed.  Reducing prose alone does not warrant another trial.

A checked semantic summary now provides the required smaller proof unit for Demo 7's counter-transfer helper.  The annotation consumer proves a complete store-preserving identity theorem after recognizing the initial pair, both counter transitions, exit condition, returned accumulator, and store-neutral suffix.  Three runs completed in 386.828, 371.243, and 354.004 seconds, giving a 371.243-second median that is 28.7 percent below the prior retained median.

The promoted proofs contain 72, 68, and 67 lines, and every agent used the summary as the scalar premise of the complete singleton wrapper.  Their journals contain no target-side reconstruction of the loop invariant, hidden locals, transition witnesses, or termination measure.  This result validates checked proof summaries as the next development direction.

Demo 8 supplies the second compiler-generated layout.  Its helper carries an unrelated audit accumulator, has 23 locals and accumulator coordinates `[4, 5, 6]`, and returns slot two; the generalized recognizer discovers the remaining-and-result pair from checked transitions.  A fresh end-to-end run used the generated summary on the first proof edit, completed Stage 5 in 313.253 seconds, and produced a 70-line independently verified proof.

The deterministic starter now composes a checked singleton-wrapper match with the generated summary for that wrapper's exact callee.  Three fixed Demo 7 runs completed in 232.164, 201.366, and 204.537 seconds, giving a 204.537-second median that is 44.9 percent below the checked-summary median.  Each agent received only the two formal-result equations, accepted its first edit, and passed separate exact-artifact verification.

A fixed-artifact Demo 8 trial used the same complete starter and generated three-accumulator theorem, then passed after one edit covering only the two formal-result equations.  It took 477.180 seconds against the earlier run's 313.253 seconds, an increase of 52.3 percent, and produced 72 lines instead of 70.  The trial confirms applicability across layouts but provides no timing evidence for that artifact.

The Demo 7 distribution promotes the composition mechanism, while the identity-producing counter-transfer recognizer remains motif support.  The shared `CounterTransition.postTestProgram_spec` theorem is independent of a generated function, and Demos 7 and 8 exercise different local layouts, but the semantic motif remains narrower than general scalar-loop verification.  Further loop summaries should share the checked composition mechanism without expanding this theorem to include their application semantics.

A residual-normalization screen unfolded the generated expected function and reduced size-one arrays after complete composition.  Demo 8 accepted an untouched 67-line starter in 219.561 seconds, while two Demo 7 Codex runs accepted the same proof in 242.798 and 211.558 seconds.  The isolated Demo 7 screen could not beat the retained median, so those accepted packages remain worked examples.

Direct starter acceptance changed the execution cost of that proof structure.  Leanexegen now runs the full outer proof check before Codex when checked composition predicts a complete starter, accepts a successful check directly, and falls back only after an ordinary proof failure at the first Lean target.  Three Demo 7 runs took 112.152, 125.103, and 156.268 seconds, giving a 125.103-second median that is 38.8 percent below the prior complete-starter median, while an independent Demo 8 run took 212.727 seconds with zero Codex time.

## Phase 4: Test source-proof guidance

The first source-assisted experiment should use ideal annotations written from a real source proof.  `SEMANTIC_HINTS.json` should name abstract state fields, invariant, rank, branch guards, state updates, terminal rule, mathematical dependencies, and a tentative source-to-target local map.  It must exclude target tactic scripts, accepted `Behavior.lean` excerpts, and `wp_peel` sequences.

The artifact proof may read this file during generation but cannot import it.  The published artifact proof must verify after the hint file, Source proof, compiler trace, and generator state have been removed.  Compiler mappings remain untrusted until checked target symbolic execution establishes the claimed region and local correspondence.

- [ ] Write and check a demo-1 source theorem.
- [ ] Author ideal semantic hints from that proof without consulting the accepted target script.
- [ ] Run three fixed reproofs with those hints and compare stage-5 medians.
- [ ] Add a typed `SourceHintBundle` only if ideal hints reduce median time by at least 25 percent.
- [ ] Extend compiler output with a separate proof map for source names, IR slots, scratch ranges, calls, and emitted region candidates.

Proof-term mining should begin only after ideal hints succeed.  Lean proof terms reliably expose constant dependencies, recursors, and induction arguments, but they do not reliably retain intended variable meanings or loop invariants.  A typed source annotation API is preferable when the experiment needs those concepts.

## Phase 5: Generate a source-free semantic capsule

A semantic capsule contains program-specific mathematics without Source, compiler, IR, WASM, or lowering declarations.  Demo-1's capsule should define factorization state, abstract transitions, preserved prime-factor count, progress cases, rank, and terminal equality with `FormalSpec.expected`.  The target proof then establishes that each exact WASM branch implements one capsule transition.

The current `Behavior.lean` already identifies the division.  Number-theoretic lemmas and abstract transition facts belong in `Behavior.Semantics`, while target local frames, weakest-precondition steps, allocator execution, and memory reconstruction remain target obligations.  A source-aware agent may propose the capsule, but Lean checks the retained declarations as independent mathematics.

- [ ] Define module-role import policies for semantic capsules.
- [ ] Generate and check `Behavior.Semantics` in a workspace without Source.
- [ ] Give `Behavior.Func0` the capsule theorem signatures instead of source material.
- [ ] Measure capsule-generation time, target-proof time, and their sum.
- [ ] Reject any transitive dependency on Source, IR, extraction, emission, or lowering declarations.

Phase 5 passes when the artifact-only package verifies after generation-only files are removed and the target agent uses capsule transitions directly rather than reproving the same mathematics.  The scorecard must distinguish invariant discovery, capsule construction, target-proof work, proof structure, reuse, and total time.  A checked capsule may remain a worked example after one use, while repeated successful use supports promotion to the default imported kit.

## Phase 6: Add target certificates and a VCG

The larger change replaces free-form target scripts with annotations checked by deterministic target machinery.  A first target certificate should name exact regions, function summaries, loop invariants, ranks, branch transitions, local representations, memory frames, and ABI results.  A source proof, compiler trace, or model may propose the certificate, while the checked conclusion still names the exact `Program`.

The first VCG should handle straight-line instructions and branches, stop at calls and loops, accept explicit summaries and invariants, and label obligations with structural paths.  It should construct proof terms from Talos weakest-precondition lemmas or use a verified checker whose soundness theorem yields `TerminatesWith`.  Unresolved goals should concern application semantics and bounded machine arithmetic rather than stack administration.

- [ ] Pilot straight-line and conditional fixtures.
- [ ] Generate stable branch obligations for demo-1 function 0.
- [ ] Accept the semantic capsule's invariant, rank, and transition theorems.
- [ ] Compose the checked function summary with the semantic array wrapper.
- [ ] Apply the same checker to demo-2 with new annotations and no new instruction-proof architecture.

Phase 6 passes when three fixed reproofs have a median below 900 seconds.  The VCG should stop if its obligations retain most of the current target script or an individual check becomes more than 20 percent slower than its focused handwritten counterpart.  Artifact-derived target normalization follows only if the VCG still exposes enough generated local and stack structure to dominate proving time.

## Package and dependency enforcement

Package schema 4 includes Source even though the artifact theorem's import closure excludes it.  A later schema should separate the final proof payload from generation provenance, allowing an optional linked generation record for Source, compiler reports, hints, and model telemetry.  `leanexegen verify` should consume only the exact artifact, final proof modules, formal specification, proof-kit identities, and deterministic artifact support.

Module roles should include formal specification, exact program, artifact support, semantic capsule, target certificate, behavior units, and final result.  Each role needs an explicit import policy.  A Lean-side declaration-dependency audit rooted at `artifact_correct` must reject Source and configured compiler namespaces even through transitive imports.

- [ ] Separate proof payload from generation provenance.
- [ ] Add module-role import policies and transitive declaration-dependency checks.
- [ ] Test direct Source imports, transitive Source imports, IR or lowering imports, renamed compiler modules, unsupported proof-kit modules, axioms, and `sorryAx`.
- [ ] Rebuild a published proof after removing the complete generation record.

These changes protect the meaning of source-assisted experiments.  They should proceed alongside the timing work and must not delay early fixed-artifact measurements.  A timing improvement that crosses the declared artifact-only boundary fails regardless of its duration.

## Remote `dev` Lean lane

The `dev` host has 32 CPUs, 61 GiB of memory, no swap, and 264 GiB free under `/mnt/vq`.  Its semaphore-capable runner is `/mnt/vq/sol/tools/leanrun`, using `/mnt/vq/leanrun-locks`; the older runner under `~/vq` has no semaphore and must not run leanexe work.  A bounded diagnostic confirmed a 24-GiB memory limit, zero swap, a 16-CPU quota, and working user cgroups.

The host now has an x86-64 Lean 4.31.0 toolchain under `/mnt/vq/elan` and a source-only leanexe checkout under `/mnt/vq/leanexe`.  Its persistent Talos and Mathlib caches can elaborate and check proof modules under the remote runner.  The remote role remains Lean development rather than complete leanexegen timing.

The local machine is AArch64 and `dev` is x86-64.  Source transfer must exclude `.git`, every `.lake` directory, and native build output, with persistent x86-64 caches built on `dev`.  Initial leanexe work should set `VQ_JOBS=1` and use one stable remote checkout; two remote jobs require separate checkouts and build trees.

After provisioning, the remote runner invocation should fix the toolchain, timeout, slot count, and lock directory explicitly.  A repository wrapper should construct this command from ordinary arguments so callers do not reproduce quoting or environment setup.  The wrapper must reject a missing toolchain, mismatched source manifest, unavailable cgroup, or unavailable semaphore before starting Lean.

```sh
ssh dev '. ~/vq-limits.env
export VQ_TOOLCHAIN=/mnt/vq/elan/toolchains/leanprover--lean4---v4.31.0
export VQ_TIMEOUT=<seconds>
export VQ_JOBS=1
export VQ_LOCKDIR=/mnt/vq/leanrun-locks
cd /mnt/vq/leanexe
exec /mnt/vq/sol/tools/leanrun <lean-or-lake-command>'
```

- [x] Install x86-64 Lean 4.31.0 under `/mnt/vq/elan` after approval.
- [x] Create `/mnt/vq/leanexe` and synchronize source-only manifests.
- [x] Build and retain the remote 4.31.0 Talos and Mathlib cache.
- [x] Add a checked `tools/leanrun-dev` interface with toolchain, source-manifest, cgroup, lock, and timeout preflights.
- [x] Fix or override the unsafe eight-slot default in `/mnt/vq/vq-remote-lean`.
- [ ] Run one local and one remote Lean development check concurrently after both runners pass their diagnostics.

Remote checks increase development throughput but do not enter local timing comparisons.  If remote runs later become the benchmark lane, leanexe needs a fixed remote resource profile and a separate baseline series.  The full model session, Lean checks, and outer acceptance must then run under that single declared lane.

## Execution order and concurrency

Phase 0 begins first and should not delay the semantic allocator work.  Program-map schema design, remote provisioning, semantic runtime theorem extraction, and telemetry can proceed concurrently because they own different files and machines.  Split orchestration waits for the map schema, while the singleton wrapper waits for the allocator theorem.

| Agent | Initial task | May run concurrently with |
|---|---|---|
| Orchestration agent | Benchmark fixture, telemetry, stage reports | Map, runtime, and remote agents |
| Artifact-map agent | Program traversal, fingerprints, checked regions | Telemetry and runtime agents |
| Runtime agent | Empty-search bump theorem and adapter | Telemetry and map agents |
| Source agent | Demo-1 source theorem and ideal hints | Artifact-only streams |
| Remote agent | 4.31.0 lane setup and remote checks | One local Lean job |
| Benchmark agent | Fixed local reproof series | Remote Lean development checks only |

Each Lean host admits only the jobs allowed by its runner and semaphore.  Agents must use separate remote worktrees before concurrent remote builds.  The benchmark agent owns the local timing lane during a series so unrelated local Lean work cannot alter wait time.

## Promotion and stopping rules

Repeated fixed reproofs are required before claiming a proof-time distribution or median improvement.  A single accepted run can establish theorem applicability, annotation linkage, structured retrieval, or a proof-construction result when the evidence is stated at that scope.  Every run must preserve acceptance and exact artifact identity, and every reported timing must include failed attempts governed by the same experiment.

LTG review records role, scope, and evidence status separately.  Role is checked proof asset, annotation support, or worked example; scope is generic semantics, a compiler or runtime motif, or benchmark-local content; evidence status is promoted, provisional, or rejected.  Promotion requires two independently verified consumers of the same semantic statement unless the declaration states a direct theorem about the pinned Talos semantics, while proof time, proof structure and size, retrieval behavior, agent revisions, and compiler-derived evidence determine its selection priority and later refinement.

A phase stops when logical dependencies cross the artifact-only boundary, accepted-proof reliability falls, or repeated evidence shows that the proposed interface preserves the same detailed target obligations without improving another evaluation dimension.  A proving-time increase weighs against an interface but does not erase accepted structural or cross-program evidence, and a theorem with adverse timing may remain in structured LTG at a lower selection priority.  Checked lemmas, tactics, guidance, and worked examples may enter the catalog without a measured timing gain when their scope, evidence, and retrieval policy state the limitation.

The plan succeeds when the artifact-only method proves demo-1 in a median below 900 seconds and applies to demo-2 through new semantic annotations rather than new instruction-level machinery.  The retained package must still prove the exact artifact theorem and pass every import, dependency, axiom, byte, and independent verification check.  The theorem-transport route may produce a separate source-dependent exact-byte theorem without changing this completion condition.
