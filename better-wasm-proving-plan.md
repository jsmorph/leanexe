# Plan for Faster Direct WASM Proof Generation

| Field | Value |
|---|---|
| Date | 2026-08-05 |
| Optimization metric | Median wall-clock time from stage 5 start to its first accepted proof |
| Fixed artifact | SHA-256 `dbced77ae7a692ce49e98cb58721cb3c05a3712925e31685c4fd08dba4181be7` |
| Retained baseline | `.lake/leanexegen-runs/demo1-timing-1` |
| First faster result | `.lake/leanexegen-runs/demo1-timing-2` |

Stage-5 wall-clock time to the first accepted proof is the sole optimization metric.  Proof size, theorem count, verifier duration, library size, and intermediate command counts may explain a timing result, but none can promote a variant.  Independent verification remains a correctness gate rather than a performance metric.

The [technical analysis](better-wasm-proving.md) describes the available mechanisms and their logical boundaries.  This plan orders experiments by expected effect on proof time, beginning with measurement and complete semantic regions rather than additional leaf arithmetic.  Every promoted method must concern the same frozen formal specification, `Program`, WASM, Codex identity, model settings, toolchain, machine profile, and cache policy.

## Evidence and target

The retained timing-1 package took 3,516.775 seconds in stage 5.  The controlled timing-2 reproof changed only the proof kit and guidance, used the same WASM bytes, and took 1,964.130 seconds.  The 1,552.645-second reduction equals 44.15 percent, although one run does not establish a stable distribution.

Timing-1 produced a 579-line proof, while the faster timing-2 run produced 591 lines.  This result confirms that proof length cannot select an optimization.  The immediate task is to reproduce the timing reduction, then replace complete discovery and execution regions so later phases can make larger reductions.

The unchanged word-address series took 1,964.130, 360.144, and 2,249.443 seconds, for a median of 1,964.130 seconds and a range of 1,889.300 seconds.  Three proofs using `Project.ProofKit.FixedArrayAllocator.region_spec` took 2,556.812, 1,134.008, and 941.494 seconds.  Their 1,134.008-second median passes the 1,758-second semantic-workbench gate and is 42.3 percent below the word-address median.

Three proofs using `Project.ProofKit.FixedArraySingleton.region_result_spec` took 680.396, 436.403, and 489.993 seconds.  Their 489.993-second median is 56.8 percent below the allocator median and 75.1 percent below the word-address median.  The demo-1 result passes the longer 900-second target through a checked runtime-region theorem, while the plan still requires application to demo-2.

## Invariants

The final artifact-only theorem must continue to mention the exact Talos module derived from the embedded WASM bytes.  Proof generators, source proofs, compiler traces, structural maps, retrieval tools, and language models may propose evidence.  Lean must check every retained target claim against the exact `Program` and the existing decoded-byte equality.

The artifact-only proof closure may contain `FormalSpec`, neutral mathematics, a source-free semantic capsule, the exact `Program`, checked structural declarations, proof-kit modules, target certificates, and artifact-support modules.  It must exclude Source, source theorem declarations, compiler IR, extraction declarations, emitter declarations, compiler traces, and lowering theorems.  Direct composition with a source theorem and checked lowering remains the separate theorem-transport result described in [Theorem Transport](plans/theorem-transport.md).

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

The [compiler-theorem analysis](docs/compiler-theorem-bridge.md) defines the first restricted theorem boundary and records the current compiler inventory.  Its scalar reification increment now covers Demo 1's guard and complete loop body, proves production emission agreement, emits versioned descriptor data, and generates an exact decoded-region equality.  The remaining experiments add semantic information only when a neutral artifact-side checker or theorem can verify the same information against the descriptor and exact WAT-derived program.

| Experiment | Compiler theorem or analysis | Artifact-side result | Proof work removed | Acceptance test |
|---|---|---|---|---|
| Scalar emission | Successful IR reification emits the descriptor program | Exact region equality and `ScalarTransition.whileProgram_spec` | Instruction decoding, checked division expansion, branch shape, assignment order, and scratch handling | Full annotation trial was 83.0 percent slower; scalar-only result pending |
| Effects and frames | Descriptor reads, writes, and scratch interval bound all local changes | Recomputed frame certificate and preservation lemmas | Local-frame reconstruction and unchanged-local proofs | Mutation rejection and lower time where descriptors retain untouched locals |
| One-step semantics | IR evaluation agrees with descriptor evaluation for one loop step | Closed transition equations over application locals that hide scratch state | Descriptor evaluation, branch update algebra, scratch-state equality, and local-numbering discovery | Lower median time on Demo 1 and a held-out scalar loop |
| Annotation locations | Annotated composition preserves path and interval coordinates | Exact coverage and non-overlap certificate | Region navigation, decomposition, and continuation reconstruction | Every coordinate mutation fails before behavior proving |
| Cut-point graph | Emitted fragments compose into loop-head, call, allocation, and return transitions | Checked graph over exact decoded regions | Control-flow discovery and repeated composition scripts | Proof obligations contain application predicates rather than instruction lists |
| Range facts | Abstract interpretation proves intervals, nonzero divisors, and representation bounds | Neutral checker validates each fact over descriptor transfer | Repeated fixed-width normalization and range searches | Total proof time falls on two structurally different artifacts |
| Source-proof projection | Proven source relations map to IR slots and cut points | Candidate invariant or source-free semantic capsule rechecked over the descriptor | Invariant discovery and mathematical lemma selection | Artifact closure excludes compiler declarations and combined generation time falls |

The experiments proceed in table order because each row supplies evidence and theorem structure needed by the next.  A compiler-side proof alone does not qualify an experiment: exact decoded-region agreement, compiler-free artifact closure, emitter byte compatibility, and independent package verification remain required.  The timing gate compares complete Stage 5 duration under one Codex version, reasoning level, machine profile, cache policy, formal specification, and WASM artifact.

The first fixed-artifact annotated trial increased Demo 1 Stage 5 from 2,017.931 to 3,692.913 seconds.  The package combined the scalar descriptor with length-dispatch and direct-call recipes, and its journal records substantial wrapper-proof work alongside descriptor-evaluator and scratch-state obligations.  A scalar-only annotation package must run before this result can accept or reject the scalar-emission row, while checked, scratch-hiding transition equations remain the next implementation if that isolated result is neutral or slow.

- [x] Reify Demo 1's scalar IR into a neutral descriptor and prove production emission agreement.
- [x] Generate and Lean-check exact descriptor equality against Demo 1's decoded WAT region.
- [x] Preserve Demo 1's frozen WASM bytes and pass execution, serializer, and aggregate Talos gates.
- [ ] Record a matched Codex-version baseline and three scalar-only descriptor trials; the baseline and first confounded full-annotation trial are retained.
- [x] Add descriptor effect sets and generic artifact-side frame theorems.
- [ ] Generate closed one-step transition equations and test whether Codex uses them.
- [ ] Freeze a held-out scalar-loop demo before exposing descriptor data.
- [ ] Add checked annotation-location composition after the semantic rows pass their timing gates.
- [ ] Pilot a checked cut-point graph on two artifacts with different control-flow structure.

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

Phase 1 passes when a one-instruction mutation rejects the old structural module, a focused `Entry` edit does not rebuild `Func0`, and three fixed reproofs have a lower median than the promoted Phase 0 variant.  If additional Codex sessions cost more time than module checkpoints save, adjacent units should merge while their checked interfaces remain.  Proof splitting remains useful only when stage-5 time falls.

## Phase 2: Replace complete runtime regions

`Project.ProofKit.FixedArrayAllocator.region_spec` now covers the inlined empty-free-list search, bump allocation, page decision, six header stores, allocator-counter update, and returned array root.  The theorem has no CLOB dependency and parameterizes the fixed-array capacity and stride.  An exact demo-1 check identifies the emitted instruction slice with `FixedArrayAllocator.region 1` and instantiates the theorem against the frozen `Program`.

`Project.ProofKit.FixedArrayRuntime` should define the canonical program template.  `Project.ProofKit.AllocationRegion` should contain readiness and result records plus a continuation-style `wp_empty_search_bump` theorem.  The generated structural module should prove that the concrete demo region equals the canonical template before the artifact proof applies the semantic theorem.

The following theorem should cover the complete singleton-array ABI wrapper.  It accepts an input representation, scalar callee summary, allocator readiness, and an equation connecting the scalar result to the expected singleton element.  Its conclusion handles both the unchanged non-singleton branch and the newly allocated singleton branch.

- [x] Distill the neutral empty-search bump theorem from the established runtime proofs.
- [ ] Bundle memory, global, page, pointer, frame, and representation premises into small records.
- [ ] Add a checked adapter for the existing CLOB consumer.
- [x] Apply the theorem to demo-1 through an exact region equality.
- [x] Add the parameterized singleton-wrapper theorem and demo-1 adapter.
- [ ] Use demo-2 as the second consumer before declaring the wrapper API stable.

The demo-1 Phase 2 timing and proof-coverage gates have passed.  The accepted singleton proofs no longer symbolically execute the free-list loop, no-growth branch, header stores, allocator-counter update, returned-root assignment, output stores, or output-array reconstruction.  Demo-2 remains the required second consumer before treating the fixed wrapper interface as stable.

## Phase 3: Supply exact proof-library selections

The current task receives about 31 KB of catalog and strategy prose, and demo-1 selects every strategy section.  A proof agent needs exact declarations and examples for its current checked region.  More general prose will increase selection work without establishing a target fact.

A machine-readable catalog should record declaration names, signatures, modules, structural tags, premises, compatible fingerprints, and one checked application.  A `CatalogCheck.lean` module should check every advertised declaration and example.  `tools/leanexegen-proof-query.js` should select the smallest useful set from the current proof unit and exact region map.

- [ ] Define and check the catalog schema.
- [ ] Index the current proof-kit modules and semantic runtime theorems.
- [ ] Generate `PROOF_GOAL.json` and `PROOF_SELECTION.json` per proof unit.
- [ ] Rank the relevant theorem among the first three results for every demo-1 unit.
- [ ] Exclude unrelated retain, release, CLOB, LEB128, and copy guidance from demo-1 tasks.

Phase 3 passes only when the selected context reduces median stage-5 time.  A retrieval miss may fall back to the full checked catalog, but telemetry must record the miss.  Context size serves as an explanatory measure rather than an acceptance measure.

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

Phase 5 passes when the artifact-only package verifies after generation-only files are removed and the complete capsule-plus-target process lowers median proving time.  The target agent must use capsule transitions directly rather than reproving the same mathematics.  A capsule that only moves proof text without reducing time should be removed.

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

Every experimental variant receives three fixed reproofs before promotion.  Each trial runs until the first accepted proof or the declared timeout, and every failed attempt consumes its full measured time.  A variant wins only by lowering median stage-5 wall-clock time while preserving acceptance and the exact artifact identity.

A phase stops when median proving time rises by more than ten percent, success rate falls, target obligations remain as detailed as the current script, or logical dependencies cross the artifact-only boundary.  Checked lemmas may remain internal when they help other proofs, but they should not enlarge the default catalog without a measured proving-time gain.  Prompt changes and shorter proofs provide no promotion evidence.

The plan succeeds when the artifact-only method proves demo-1 in a median below 900 seconds and applies to demo-2 through new semantic annotations rather than new instruction-level machinery.  The retained package must still prove the exact artifact theorem and pass every import, dependency, axiom, byte, and independent verification check.  The theorem-transport route may produce a separate source-dependent exact-byte theorem without changing this completion condition.
