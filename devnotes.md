# Development Journal

## 2026-08-11: Documentation consolidation

The maintained documentation now assigns current language behavior, compiler architecture, artifact proving, annotation semantics, status, and active work to separate authority documents.  The consolidation removed superseded design reports and historical work queues after migrating their current facts.  Demo 1 now identifies its scalar ABI as the predecessor of the current array interface, while Demos 2 through 11 remain the current-interface examples.

The review corrected three substantive claims.  The `leanexegen` verifier accepts package schemas 3 through 7, the current release record describes an older input identity, and the repository has selected compiler-emitter equalities rather than a general compiler-correctness theorem.  The Talos proof inventory and release documentation now distinguish dated successful gate evidence from the current tree.

`tools/check-docs.js` defines the maintained Markdown set, verifies local links, rejects references to removed documents, and rejects absolute `/tmp` workspace examples while allowing the machine-wide Lean lock path.  It excludes frozen proof-task copies and journals because those files record the context and observations of earlier runs.  Current command examples use repository-local `./tmp` workspaces.

Checks run:

- [x] `git diff --check` accepted the consolidated documentation.
- [x] `tools/check-docs.js` accepted 77 maintained Markdown files.
- [x] `node --check tools/check-docs.js` accepted the documentation checker.
- [x] Repository tool usage output matched the documented current command forms.
- [x] `tools/artifact-release.js refresh` recorded input digest `e175bf46d1d2102da862d57464d1a8db5c64a681da1c084653386331292e7651` and cleared stale gate receipts.
- [x] `tools/artifact-proof.js check-all` passed all twenty artifact identities, embedded-byte checks, artifact theorems, behavioral specifications, and manifest declarations for the refreshed digest.
- [x] `tools/artifact-conformance.js check` passed twenty-five execution files and fifteen invalid modules with the one configured Talos imported-memory warning.
- [x] A second `tools/artifact-release.js refresh` consumed both matching warm-gate receipts and reduced the blocker count from four to two.

The first cold-checkout attempt reached `Project.ClobLimit.ArtifactBytes` before the aggregate `Project.Artifact.Binary.CheckFile` target exhausted its 15-minute limit.  The target imports all twenty embedded-byte modules, so a clean checkout charged the complete shared Talos build and every large byte-literal elaboration to one timeout boundary.  No theorem or byte comparison failed.

The artifact driver now builds each manifest-declared embedded-byte module as a separate 30-minute target before building the aggregate checker.  This division preserves the exact byte-comparison program and gives the initial shared dependency build and each large literal an independent limit.  Because `tools/artifact-proof.js` belongs to the release-input identity, the changed driver requires new warm receipts, a new immutable revision, and another cold run.

The revised warm artifact gate passed after the first separated byte-module target completed the 3,009-job shared build and the remaining nineteen reused those outputs.  All later artifact, behavioral-specification, and declaration checks passed.  The conformance gate also repeated its 3,853 passes, six configured failures, 627 skips, twenty-five Wasmtime file passes, and fifteen exact invalid-module classifications for release-input digest `23b34f98bc9da1c9c6e3801af0c20303380f3beacf45d0e1c3c2c678ddadef35`.

The next cold attempt passed the complete divided byte phase, then exposed the same shape inside `Project.AssocList.ArtifactTranslation`.  Its generated program, decoded module, raw-cache equality, decode theorem, and validation module each completed, but their sequential work exhausted the encompassing 15-minute artifact-target limit before the final translation module.  The driver now builds those five manifest-derived inputs as separate 30-minute targets for every package before applying the unchanged 15-minute limit to the final artifact theorem.

The first warm check of that division found the older GCD package layout, which uses `Project.Gcd.Artifact` in place of the separate `ArtifactValidation` module used by the other nineteen packages.  The driver now includes only prerequisite modules that exist for the registered package and includes either layout without special-casing a case name.  The manifest-defined program module remains mandatory for every package.

The layout-aware warm gate passed all twenty exact-artifact packages, behavioral specifications, and manifest declarations on 2026-08-12.  The conformance gate passed the same day with its configured imported-memory warning, and `tools/artifact-release.js refresh` consumed both receipts for release-input digest `6db591ec2d359cdab4bfd51b1f99b7e4477da338956e7e2ede2c9a861e725d1c`.  Release inspection now reports only the immutable source revision and its cold-checkout result as blockers.

Recording the immutable source revision exposed a state assumption in `test/artifact_release.js`.  The test expected the earlier two-blocker draft record literally, although the release validator derives both status and blockers from the evidence fields.  The test now derives its expectation through the same exported rule, so it covers the one-blocker transition and the final ready record.

The cold gate at source revision `c956e6bd2d359774a0c2b40da21dde75c43397d2` reached the 30-minute limit for `Project.Gcd.ArtifactBytes` after completing 2,996 shared jobs.  The byte module produced no diagnostic; its import of the artifact translator pulled in the `CodeLib` umbrella, which in turn compiled the complete Talos interpreter and weakest-precondition library inside the first package boundary.  The driver now builds `CodeLib` once under a separate 60-minute shared-library boundary before the artifact translator or any package target.

A narrower `Interpreter.Wasm.Syntax` import suffices to compile the translator, but `Translate.lean` belongs to the normative verifier-source digest recorded by every immutable package.  Adopting that source change would require reissuing the twenty package manifests.  The release work therefore preserves the packaged verifier source and changes only the proof driver's build boundaries.

The explicit shared-library target completed 3,001 jobs under its 60-minute boundary.  The renewed warm artifact gate then passed all twenty packages, behavioral specifications, and declaration checks, while the matching conformance gate repeated its accepted corpus result.  Refresh consumed both receipts for release-input digest `7c5b330b33d365959427ba60c1fa0f5ebbc5ee3b4d959b0b5c454953167cc1fd` and restored the two expected pre-cold blockers.

## 2026-08-11: Fold-composition work begins

The current [artifact-proving reference](docs/artifact-proving.md) and root [development plan](plan.md) retain the unresolved obligations identified across the addition, multiplication, and XOR fold journals.  The first experiment added a general equality interface for `Wasm.Locals`, including operand-stack replacement projections.  The second experiment added a generic arbitrary-postcondition singleton-result theorem and an exact annotation-generated adapter after the frame interface passed fixed-proof checks.

A focused Lean probe confirmed that the pinned Talos `Wasm.Locals` structure exposes `Wasm.Locals.mk.injEq` but no named `Wasm.Locals.ext` theorem.  Demo 11's journal records failed attempts to use record syntax and the `ext` tactic before `convert` and reflexivity closed an exit-frame equality.  This evidence justifies a small generic theorem whose statement depends only on the three fields of `Wasm.Locals`.

The evaluation holds every artifact and mathematical theorem fixed during manual substitutions.  A later fresh proof screen will measure retrieval, edited checks, theorem use, proof structure, and Stage 5 time together, while an independently verified exact-artifact theorem remains mandatory.  Tactic indexing and a new held-out fold follow only after the two semantic interfaces stabilize.

Checks run:

- [x] `tools/leanrun --timeout 5m lake -d proofs/talos/lean env lean /tmp/leanexe-locals-probe.lean` confirmed the missing extensionality theorem and accepted the proposed three-field proof shape.
- [x] `tools/leanrun --timeout 10m lake -d proofs/talos/lean --no-ansi build Project.ProofKit.Frame` accepted `Frame.ext` and the four `withValues` projection theorems.
- [x] `tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build Project.ProofKit.LTGCheck` accepted every indexed declaration, including the new frame interface.
- [x] Verify fixed Demo 9 and Demo 11 proof substitutions.

## 2026-08-11: Exact singleton-result adapter

`FixedArrayFold.singletonResultProgram_spec_to` executes the result-local write, singleton payload store, and final root transfer for an arbitrary exact postcondition.  The annotation consumer generates `<fold>_singleton_result_spec` only when the complete singleton-result suffix and guarded loop edge match the decoded program.  The generated theorem discharges local-layout, result-placement, root-preservation, and destination-validity premises through the exact continuing-frame accessors.

A regenerated Demo 11 annotation package checked the adapter against the unchanged 1,979-byte WASM module and digest `4f56fd45fe246f3199dc81169235aa0673659b3b2e82e4beeb4c1d910501bd64`.  A manual proof substitution applies the generated theorem directly to the public branch postcondition and closes the equivalent exit frame with `Frame.ext`.  The complete `ArtifactResult` target passed under the repository Lean limits.

The manual proof decreased from 676 to 580 lines, from 2,798 to 2,350 whitespace-delimited words, and from 34,648 to 30,182 bytes.  It removes the proof-local singleton-result theorem and postcondition consequence theorem while retaining the XOR fold equation and represented-array proof.  The experiment establishes checked applicability and a smaller proof structure, but it provides no proof-generation-time measurement.

The same generated adapter passed in a fixed Demo 9 wrapping-sum proof.  The complete proof decreased from 616 to 569 lines, from 2,541 to 2,404 words, and from 30,901 to 28,245 bytes, while retaining artifact digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  Independently verified packages now preserve both manual substitutions without carrying the telemetry from their predecessor proofs.

A fixed Demo 10 wrapping-product proof applies the same adapter directly to its public valid-branch postcondition.  The complete proof decreased from 600 to 553 lines, from 2,371 to 2,162 words, and from 30,568 to 28,254 bytes, while retaining artifact digest `a981c7882a51a0660e6dd1e17956b958f7b2e25cbc30618d12458601ef2d4baa`.  Independent package verification accepted the edited source and exact artifact theorem.

## 2026-08-11: Fresh fold-completion screen

A fresh Demo 9 proof task received the structured LTG, exact annotations, generic fold-completion theorem, and generated singleton-result adapter.  Its first catalog search selected the completion entry, and the accepted proof applies `function_0_array_fold_0_singleton_result_spec` directly to the public result.  Separate package verification accepted the proof over the unchanged 1,979-byte artifact and digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.

Stage 5 took 1,992.546 seconds, including 1,922.343 seconds in Codex and 54.378 seconds in outer acceptance.  The measurement is 10.7 percent below the prior frame-accessor screen, 4.3 percent below the retained fold-structure proof, and 1.0 percent above the best guarded-back-edge screen.  The 526-line, 2,039-word proof removes 90 lines and 502 words from the frame-accessor proof and 43 lines and 365 words from the manual fold-completion substitution.

The journal records fourteen successful diagnostic cycles.  The completion adapter closed the loop-exit suffix without a proof-local theorem, while capacity and allocator projections still required reductions, and the strict loop body required the invariant to carry annotation local 18, `releaseReadyLocal`.  The next interface review will consider generic capacity-frame, allocator-root, and annotation-selected loop-local accessors before a Demo 10 transfer screen.

`FixedArrayCapacity` now supplies combined and internal getters for the written normalized capacity.  `FixedArrayAllocatorWindow` supplies parameter, local-length, and operand-stack projections together with a returned-root getter for any offset and trailing-local count.  Lean accepted both modules and the generated declaration check, and structured LTG exposes each new declaration through the capacity or allocation entry.

The existing fold annotation already generated a checked getter for local 18, so another semantic theorem would have duplicated available evidence.  The recipe generator now labels continuing-frame getter purposes with compiler roles, making `releaseReadyLocal` searchable by name.  A regenerated Demo 9 annotation package names `function_0_array_fold_0_continuing_frame_get_18` for that role and passes independent package verification.

## 2026-08-11: Demo 10 projection transfer

The controlled Demo 10 run retained the specification, source, 1,979-byte WASM module, digest, toolchain, and model configuration.  Its first allocation-boundary search selected the new capacity and allocator-root projections, and the accepted proof uses both declarations in the valid and invalid branches.  It also applies the generated fold-completion adapter, shared fold-body theorem, exact loaded-frame equality, and compiler-generated multiplication transitions.

Stage 5 took 1,979.854 seconds, including 1,912.675 seconds in Codex and 59.059 seconds in outer acceptance.  This is 5.7 percent below the frame-accessor screen, 3.5 percent above the fold-body screen, and 24.0 percent above the retained primary proof.  Independent verification accepted the package and confirmed artifact digest `a981c7882a51a0660e6dd1e17956b958f7b2e25cbc30618d12458601ef2d4baa`.

The proof contains 684 lines, 2,875 words, and 36,126 bytes, which exceeds both the 600-line frame-accessor proof and the 553-line manual fold-completion proof.  Its fourteen diagnostic cycles include parser conflicts over two local names, a positional dependent-premise attempt despite existing guidance, and an unrestricted simplifier failure at a generated next-frame equality.  The interface transfer succeeds, while the size and iteration evidence supports structured tactic retrieval and tighter construction guidance rather than another fold-specific semantic theorem.

## 2026-08-11: Structured tactic indexing

LTG schema 2 adds a `tactics` array whose records identify the command, defining module, goal shape, premises, annotation kinds, and fallback declaration.  Validation reads the named ProofKit source and rejects an undefined command, an unlisted module or fallback, an annotation kind outside the entry, duplicate commands, or unsorted records.  Schema-1 entries remain valid and receive an empty tactic inventory during catalog loading.

The initial index covers `wp_fixed_array_length_le_dispatch_from`, `wp_block_loop`, `uint64_array_pair`, `uint64_array_singleton`, and `word_reads`.  Category JSONL records carry the structured data, while search terms include each command, module, and fallback declaration.  Metrics now distinguish five indexed commands from the twenty-seven distinct tactic commands supplied by the complete ProofKit.

The artifact-proof task now treats each indexed tactic as a choice between a command and its fallback theorem.  It compares the record's goal shape, premises, and annotation kinds with the current residual goal before attempting the command.  The journal must record the command's effect or the precise shape mismatch that caused rejection.

Checks run:

- [x] `tools/ltg check` accepted the regenerated canonical catalog, category indexes, and declaration check.
- [x] `node test/ltg.js` accepted positive records, generated-index retrieval, metrics, and rejection of a missing tactic command.
- [x] `node test/leanexegen.js` accepted the annotation, recipe, protocol, package, publication, and exit tests.
- [x] `tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build Project.ProofKit.LTGCheck` completed 3,025 jobs and accepted every indexed declaration.

## 2026-08-11: Corrected tactic-guidance screen

A fresh Demo 9 task received the corrected fold-body guidance while retaining the specification, source, 1,979-byte WASM artifact, decoded program, and digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  Its category-index search selected `wp_fixed_array_length_le_dispatch_from` after matching the branch-level goal shape, represented-array premise, and length-dispatch annotation.  The accepted first edit used that command to expose both branches without applying its fallback theorem.

The candidate then decomposed both branches and applied `FixedArrayCapacity.constantProgram_spec`.  Its next Lean check produced no diagnostic and neither the candidate nor journal changed for about twenty-two minutes, so the owned session was interrupted after approximately forty-eight minutes.  The task had not reached allocation, the annotated fold, loop induction, result construction, or the revised continuation-frame guidance.

`benchmarks/leanexegen/demo9-fold-sum/structured-tactic-guidance-censored-1` preserves the unfinished candidate, journal, generated annotation equality, frozen LTG task, recipes, selected strategies, task features, proof-library summary, and request.  This observation confirms repeated selection of the indexed dispatch tactic but supplies no evidence about the corrected fold guidance, independent acceptance, or proof-generation time.  Another unchanged run would repeat the same elaboration boundary, so the next proof experiment must divide the capacity-to-allocation composition or provide a checked reusable interface before another Lean check.

## 2026-08-09: Constant capacity and frame projection

`Project.ProofKit.FixedArrayCapacity.constantProgram_spec` executes the compiler's constant result-length capacity prefix for arbitrary `UInt64` length and stride, destination local, local-frame dimensions, store, continuation, and postcondition.  The named `normalizedCapacity` computes the aligned minimum-eight-byte capacity, while `capacityFrame` records its destination without constraining other locals.  This replaces the zero- and one-element local capacity theorems that the latest Demo 9 proof had to construct before each allocator application.

The length-dispatch consumer checks the full capacity prefix independently in its valid and invalid branches.  It requires the header, length, stride, multiplication, alignment, destination getter and setter, minimum test, replacement branch, and empty alternative to match the decoded Program.  Demo 9 produces checked branch equalities for lengths one and zero, while a test mutation of the alignment constant removes support only from the changed branch.

`Project.ProofKit.Frame.internal_getElem?_of_get` and `internal_getElem_of_get` convert a combined `Locals.get` invariant equation to the corresponding internal-list optional or indexed getter.  Demos 2, 3, 5, and 9 repeat the unfolded conversion, and the new theorem has no array, local-count, or value-type dependency.  Structured LTG now contains 20 entries, including separate capacity and frame-projection retrieval units with reciprocal links to their allocator, fold, loop, and proof-construction neighbors.

Checks run:

- [x] `tools/leanrun --timeout 15m lake -d proofs/talos/lean --no-ansi build Project.ProofKit.LTGCheck` accepted all 49 indexed declaration names, including the new capacity and frame theorems.
- [x] `tools/ltg check` accepted 7 categories and 20 entries.
- [x] `node test/ltg.js` passed catalog, index, exclusion, digest, and 10,000-record search tests.
- [x] `node test/leanexegen.js` passed the annotation, recipe, protocol, package, publication, and exit tests.
- [x] `tools/leanexegen annotate -o /tmp/demo9-capacity-annotated.proof demos/demo-9/program.proof` checked both capacity equalities against the unchanged artifact.
- [x] `tools/leanexegen verify -s /tmp/demo9-capacity-annotated.proof` independently accepted the annotated package.

## 2026-08-09: Demo 9 fold-boundary reproof

The controlled Demo 9 reproof retained the formal specification, generated source, 1,979-byte WASM module, artifact digest, and compiler annotations.  Its task-specific LTG view contained 18 entries, including the new `fixed-array-fold-structure` entry, while artifact-specific Demo 9 material remained excluded.  Codex retrieved the generic length-dispatch, fold, traversal, allocation, memory-framing, and result entries before editing the proof.

Lean accepted the proof in the first Codex session after 2,082.889 seconds, and independent package verification passed.  The preceding annotation run took 3,188.251 seconds, so the new run reduced Stage 5 time by 1,105.362 seconds, or 34.7 percent.  The accepted proof grew from 416 to 508 lines because it states two capacity-prefix theorems locally and uses explicit shared-theorem applications at the setup, traversal, result-placement, allocator, and result-store boundaries.

The journal identifies two generic follow-up targets.  A parameterized theorem and compiler-matched recipe should cover the emitted result-capacity calculation that currently requires local zero- and one-element specializations.  A frame-projection lemma or tactic should turn `Locals.get` invariant facts into internal `List.getElem?` and `getElem` facts, a repeated pattern in the proof kit and the Demo 9 loop proof.

Checks run:

- [x] `tools/leanexegen reprove -o /tmp/demo9-fold-structure-ltg-1.wasm /tmp/demo9-fold-structure-annotated-2.proof` accepted the artifact theorem and both sample executions.
- [x] `tools/leanexegen verify -s /tmp/demo9-fold-structure-ltg-1.proof` independently accepted the published package.
- [x] The published artifact retained SHA-256 `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.

## 2026-08-07: Bounded Filter Composition

The [Demo 5 baseline](demos/demo-5/README.md) took 1,635.679 seconds in Stage 5 and produced a 969-line direct proof after fourteen edited checks.  Its only checked compiler region was the bounded-length dispatch, leaving Codex to derive the input-capacity allocator, filtered-prefix loop invariant, conditional output store, dynamic result length, and empty branch.  The proof journal supplied the exact emitted program decomposition and invariant used to define the shared theorem.

`Project.ProofKit.FixedArrayFilterLt.wrapperProgram_spec` proves the canonical bounded stable filter for arbitrary maximum size and `UInt64` threshold.  The compiler recognizes the corresponding extracted IR and emits `leanexe.array.filter-lt.v1` over the complete function while preserving the nested length-dispatch region.  The JavaScript consumer validates the parameters and function boundary, constructs a checked equality with `wrapperProgram`, selects the semantic theorem, and generates the complete schema-6 artifact starter.

Three controlled reproofs retained the formal specification, source, 1,975-byte WASM, decoded Program, artifact theorem, and heap-reserve boundary.  The deterministic 70-line starter passed its first Lean check unchanged in every run and produced Stage 5 times of 86.795, 90.745, and 95.718 seconds, giving a 90.745-second median and an 8.923-second range.  The median reduces the baseline by 1,544.934 seconds, or 94.5 percent, and independent `leanexegen verify` accepted the first and third final packages.

## 2026-08-07: Artifact Heap-Reserve Precondition

The bounded filter in [Demo 5](demos/demo-5/README.md) exposed a counterexample to the former `RuntimeReady` precondition.  For input `[100]`, the final output is empty, but the compiled `Array.filter` reserves input-sized capacity before testing the element.  At a bump pointer of `2^32 - 56` with 65,536 memory pages, the former final-output bound held while the allocator failed and the artifact trapped.

The formal task now defines `heapReserveBytes : Array UInt64 → Nat` beside `expected`.  `RuntimeReady` retains its final-output representation bounds and adds separate address-space and existing-memory bounds for the stated heap reserve.  The direct artifact proof must establish each allocation premise from this reserve, which keeps the resource assumption reviewable and tied to exact emitted behavior.

Proof-package schema 6 records the expanded formal interface, while verification and controlled reproof preserve the previous declaration checks and proof starter for schemas 3 through 5.  JavaScript protocol tests cover both starter forms, an existing schema-5 Demo 4 package passes independent verification, and the schema-6 Demo 5 package passes the same verification path.  The retained Demo 5 baseline took 1,635.679 seconds in Stage 5 and identifies bounded filter allocation and loop invariants as the next shared proof target.

## 2026-08-03: Reusable WASM Proof Library Plan

The current [artifact-proving reference](docs/artifact-proving.md) and [ProofKit reference](proofs/talos/lean/Project/ProofKit/README.md) describe the shared arithmetic, memory, control-flow, runtime, and function-portability support used by artifact proofs.  The original plan recorded that generated proof sessions could not import repository-owned shared modules and received no checked declaration catalog.  The completed work added an allowed ProofKit, dependency and identity audits, a checked catalog, feature-directed context, scalar-loop and memory-runtime pilots, and continuing evidence-based distillation.

## 2026-08-03: `leanexegen` Headless Codex Orchestration

`tools/leanexegen` now owns generation through three tasks using Codex's [noninteractive mode](https://learn.chatgpt.com/docs/non-interactive-mode.md): formal specification, Lean program, and exact-artifact behavioral proof.  Each task uses one temporary workspace, one ephemeral `codex exec` session, and a JSON output schema.  The session edits its candidate and repeats real Lean or compiler checks, after which the outer process repeats the final checks in a separate workspace.

The formal task sees the request and defines `expected : Array UInt64 → Array UInt64`.  The program task sees the request and frozen formal module, while the proof task sees the request, formal module, WAT-derived Talos `Program`, and deterministic artifact-support modules.  The program workspace and every task outcome containing Source are removed after WASM freezes, so the proof task receives neither Source nor the compiler.

The orchestrator appends `${namespace}.FormalSpec.ArtifactSpec : Wasm.Module → Prop` with fixed predicates for the `Array UInt64` memory representation, allocator-ready initial stores, and terminating execution.  Generated Lean check modules require both `expected : Array UInt64 → Array UInt64` and the exact artifact-specification type before accepting the formal task.  `ArtifactResult.artifact_correct` applies that exact declaration directly to the independently decoded, validated, and translated bytes.

Successful packages retain the three accepted sources, Codex version, task summaries and decisions, one-session reports, diagnostics, source hashes, and report hashes.  Independent verification recomputes those hashes, checks the fixed formal declaration, compares the packaged file with the embedded bytes, rebuilds the artifact theorem, and audits its declarations without invoking Codex or LeanExe.  The package also retains the request, samples, host assumptions, tool pins, deterministic artifact support, and its own copy of the WASM bytes.

The proof workspace continues to use Lake 4.31.0's root-workspace `packagesDir` option to share the pinned dependency directory.  The successful dependency diagnostic completed 3,014 jobs through `tools/leanrun`; the earlier incomplete clone without that option consumed 5.5 GB before removal.  A focused Lean diagnostic accepted the fixed `expected` and `ArtifactSpec` declarations with their exact types.

Focused JavaScript tests cover the stable Codex arguments, strict output schema, single-session orchestration, formal-to-program context, proof-context Source exclusion, deterministic artifact result, task-report hashing, package validation, publication rollback, and existing kernel and axiom screens.  They also cover array samples, complete `UInt64` element validation, the `run` command, and optional proof-kit omission.  The earlier external-backend identity smoke tested a superseded path and does not establish the current headless implementation.

A live single-session identity run completed all seven stages on 2026-08-03.  The formal, program, and artifact-proof sessions ran their prescribed checks through `tools/leanrun`, and every final candidate passed the corresponding independent outer check.  The run published 1,042 bytes at SHA-256 `5561719e6bd6b2b56f2ca932ae16a5f6f518b615053bb766d8e473c4add0a725`, observed `18446744073709551615 → 18446744073709551615`, and passed a separate `tools/leanexegen verify` rebuild of `LeanExeGen.GeneratedRd3267f0041708ae6.Artifact.artifact_correct` without Codex or the compiler.

The progress stream now records each stage's UTC start time, retains publication as stage seven, and reports checked samples and the runnable command under stage eight, `Results`.  A second from-scratch prime-factor run completed all eight stages in 7 minutes 39 seconds, published the same 1,348 artifact bytes at SHA-256 `8ef01d38a73edaca6c9098876af4212bf037ff1a14ba69e186b96a884c54cdcf`, and observed `60 → 4`.  Independent verification rebuilt `LeanExeGen.GeneratedRc8c2d9f87deb0758.Artifact.artifact_correct` from the published package in about 60 seconds, without Codex or the compiler.

The repository-root `demos/demo-1/` directory retains the prime-factor walkthrough and its complete standard streams under names that do not repeat the directory name.  It contains byte-identical copies of the generated `FormalSpec.lean`, `Source.lean`, and `Behavior.lean` files as `spec.lean`, `program.lean`, and `proof.lean`.  It also retains the exact 1,348-byte compiled module as `program.wasm` and its 13,421-byte `wasm-tools 1.251.0` rendering as `program.wat`.  The documentation catalog links to `demos/demo-1/README.md`, while the editor backup and lock files beside the former documentation paths remain untouched.

The first live prime-factor run exposed a difference between LeanExe's `report` and `compile` commands.  `report` accepted the generated entry, but `compile` later rejected its local `countFactors` helper as an unsupported declaration.  The program session now performs a scratch compilation after every report, so the same session receives an extraction or emission diagnostic before stage four freezes any bytes.

`workspace-write` prevented a Codex child from connecting to the user systemd bus, and enabling command network access produced an unreliable bus connection.  `leanexegen` now starts the complete Codex session through `tools/leanrun`, which holds the machine-wide lock and applies one constrained cgroup to Codex and its children.  A nested runner verifies the inherited memory and CPU settings before executing its command, avoiding another systemd connection while preserving the resource policy.

The live proof passed before its maximum-`UInt64` sample failed because Wasmtime parses decimal `i64` arguments as signed values.  The sample shim now converts unsigned inputs above `2^63 - 1` to negative signed decimals and converts signed results back to canonical `UInt64` decimals.  The successful retained run exercised the boundary value as `-1` at the Wasmtime command line while recording the logical input and output as `18446744073709551615`.

## 2026-08-03: Clean-Checkout Artifact Proof Inputs

The warm artifact gate depended on twenty ignored `Project/<Case>/Program.lean` files that every translation target and behavioral specification imports.  Those files could not exist in a clone, so the warm result did not establish the documented cold-checkout capability.  The repository no longer ignores those files, tracks all twenty generated execution caches, and requires `cases.json` to correspond bijectively to those cache paths.

The canonical release identity now covers every Lean source under `proofs/talos/lean/Project`, `Project.lean`, the recursive local `LeanExe` import closure, root and proof Lake files, `.gitignore`, all package manifests and binaries, conformance configuration, tool pins, and the twelve local verification drivers.  The collector also requires directly invoked drivers to be executable regular files and rejects a missing or additional `Program.lean` cache.  The kernel scope audit now scans the proof tree and its two local `LeanExe` imports, and the cold command repeats that audit in the detached checkout before setup.

`tools/talos-proof.js check` generates a temporary Talos model and compares it byte-for-byte with the tracked cache before building the specification.  It does not replace a changed cache; `tools/talos-artifact.js prepare` remains the explicit refresh command.  `test/talos_cache.js` checks nonmutating comparison, changed-cache rejection, and explicit refresh, while `test/artifact_identity.js` checks all proof sources, the exact local import closure, twenty program caches, drivers, and canonical hashing.

The expanded identity invalidated the 2026-08-02 warm receipts as intended.  Fresh artifact and conformance gates passed on 2026-08-03 and recorded release-input SHA-256 `3c10b4bef4505c12ab20d9aed037e288940861f45077bf6340d7a8b79f350c4c` over 565 files.  The artifact receipt covers twenty packages, while the conformance receipt covers fifteen invalid modules and twenty-five execution files with the configured imported-memory warning.

`tools/artifact-release.js refresh` consumed both receipts and derived exactly two blockers: the current inputs have no immutable source revision, and no cold-checkout receipt can identify that revision.  The kernel scope audit passed for the proof tree and its two local imports, and `node test/run_all.js` passed 791 accepted cases, 45 expected rejections, 14 expected traps, 340 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases.  The clean-checkout run requires a committed source revision containing every tracked cache and proof input.

## 2026-08-02: Verification Command Boundaries

Repository verification commands define the reusable approval boundaries.  Direct Lean diagnostics start with `tools/leanrun`, source-driven proof work starts with `tools/talos-artifact.js` or `tools/talos-proof.js`, exact-artifact proofs start with `tools/artifact-proof.js`, official-corpus checks start with `tools/artifact-conformance.js`, and release checks start with `tools/artifact-release.js`.  An approval for one of those command prefixes covers its supported subcommands and future configured cases.

Official execution files, invalid modules, assertion lines, and expected classifications belong in `proofs/talos/conformance.json`, which `tools/artifact-conformance.js check` validates and consumes.  Direct shell expansion of corpus filenames bypasses that boundary and causes the approval system to record an expanded one-off command.  Cold-checkout setup and both release gates remain inside `tools/artifact-release.js check-cold <revision>`, so the later network and temporary-checkout operation needs one repository-tool approval rather than approvals for its internal Git, download, Lake, proof, and conformance commands.

## 2026-08-02: Schema-Three Artifact and Release Evidence

All twenty artifact manifests now use schema three and name the embedded bytes, decoded raw cache, execution cache, closed artifact theorem, and concrete behavioral theorems.  Each generated `artifact_module_eq_cache` theorem contains decode and validation witnesses, a `CoreValid` proof, and equality between the validated translation and the execution cache.  The aggregate artifact gate checked the exact declaration types and printed the axiom dependencies for every manifest theorem in addition to rebuilding all twenty behavioral specifications.

The declaration audit rejects `sorryAx` and accepts only `propext`, `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, and theorem-local certificate axioms generated by `native_decide` or `bv_decide`.  The verifier-source digest covers seventeen named normative files, while the canonical release-input digest also covers toolchain pins, registries, manifests, binaries, conformance configuration, and proof-workspace inputs.  The successful aggregate receipt records twenty artifacts and release-input SHA-256 `5a9545ec3788a95a0cd3a6c73a419748ff1c4fed46d49821d85c880fbd05abaa`.

Both Lean workspaces pin 4.31.0 at commit `68218e876d2a38b1985b8590fff244a83c321783`, and that kernel accepts the archived reproduction at source `e7c533e752bf4a4cc9e0170cc0972824c46ef755:proofs/talos/lean/Examples/KernelUnsoundness.lean`.  The owner accepts this known defect for the artifact release after `tools/artifact-release.js audit-kernel-scope` found no literal `addDecl` or `inductDecl` references in `proofs/talos/lean/Project` or its two local imports, `LeanExe/Examples/AsciiDigits.lean` and `LeanExe/Examples/TalosAssocList.lean`.  This lexical audit does not cover dependencies, aliases, compiled declarations, elaborator internals, other environment-mutation APIs, or the kernel defect itself, and the release record preserves that limitation.

`tools/artifact-release.js refresh` reconstructs the package records and consumes only warm receipts whose canonical input digest matches the current repository.  The current draft has exactly two derived blockers: no immutable source revision records the implementation, and no cold-checkout receipt can identify that revision.  `check-cold <revision>` compares canonical inputs before setup and after both gates, verifies the exact Lean and dependency revisions, rejects tracked mutations, and writes a receipt only after success.

Checks run:

- [x] `tools/artifact-proof.js check-all` passed twenty schema-three packages and wrote the matching artifact receipt.
- [x] `tools/artifact-conformance.js check` passed with the exact imported-memory warning and wrote the matching conformance receipt.
- [x] `tools/artifact-release.js audit-kernel-scope` passed for the proof tree, its two local imports, and both forbidden identifiers.
- [x] `tools/artifact-release.js refresh` consumed both warm receipts and reported two blockers.
- [x] `node test/artifact_identity.js` checked the verifier membership and canonical digest vectors.
- [x] `node test/artifact_migrate.js` checked transactional migration and frozen-file identity.
- [x] `node test/artifact_release.js` checked identities, receipts, pins, results, and blocker derivation.
- [x] `node test/run_all.js` passed 791 accepted cases, 45 expected rejections, 14 expected traps, 340 standard-Lean comparisons, 62 IR comparisons, and 56 fuzz cases after the JavaScript execution guard was corrected to distinguish identifiers from strings and comments.

## 2026-08-02: Official Corpus Conformance Gate

`tools/artifact-conformance.js check` now verifies and executes a pinned official WebAssembly corpus slice.  The configuration records CodeLib revision `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`, testsuite revision `9233a0a8d5920a8d32358ee915a3662ff3385029`, Wasmtime 44.0.0, and the `function-references=y` option.  The driver also checks `wasm-tools` 1.251.0, stages each exact file in a one-file temporary corpus, and runs every Lean-based build or Talos execution serially through `tools/leanrun`.

The configuration also pins fifteen official invalid modules by file, assertion kind, source line, expected classification stage, and exact error constructor.  The driver extracts those commands with `wasm-tools json-from-wast`, strips encoder-added custom sections from text-origin `assert_invalid` modules, preserves raw `assert_malformed` binaries, and classifies all staged modules in one resource-limited Lean process.  All fifteen matched, covering malformed headers and sections, integer overflow, invalid alignment and memory limits, stack underflow, and stack-height mismatches.

The selected slice contains twenty-five files covering the accepted integer, control, call, local, memory, conversion, function, label, and expression forms.  Talos reported 3,853 passes, six known assertion failures, 627 skips, and no cascades, decoder errors, interpreter errors, or fuel exhaustion.  Wasmtime passed all twenty-five files, and every Talos failure occurred in `memory_grow.wast`.

The failing assertions import a memory exported with maximum five pages through a declaration that permits six pages.  Talos copies the memory value into the importer and computes `memory.grow` capacity from the import declaration, so the imported memory grows from five to six pages when the official semantics require `-1` and a retained size of five.  The accepted artifact-verification profile contains no imports, so the gate treats the exact six-row fingerprint as an upstream warning, removes the warning at zero failures, and rejects every changed or additional failure.

Building the pinned testsuite from a cold dependency tree required dividing the import closure before the executable target.  `Mathlib.Tactic.NormNum.LegendreSymbol`, `Mathlib.Tactic`, `Interpreter.Wasm`, `Interpreter.Testsuite.Exec`, and `Interpreter.Testsuite` built in sequence before `testsuite`, whose final build completed 5,960 jobs.  The executable's large closure comes from `Interpreter.Testsuite.Exec` importing the `Interpreter.Wasm` umbrella, which includes weakest-precondition modules and `Mathlib.Tactic`.

The asynchronous process helper now drains captured stdout and stderr and includes both streams in failure messages.  Unit tests cover output capture, async error detail, exact file selection, totals parsing, detailed failure parsing, known-issue classification, Lean command routing, and signal forwarding.  Wasmtime executions run under a five-minute timeout, while Talos executions retain the ten-minute `tools/leanrun` limit.

Checks run:

- [x] `node --check tools/artifact-conformance.js`
- [x] `node --check tools/run-process.js`
- [x] `node --check test/artifact_conformance.js`
- [x] `node --check test/run_process.js`
- [x] `node test/artifact_conformance.js` returned `checked conformance parsing, known issues, official validator cases, and file selection`.
- [x] `node test/run_process.js` returned `checked sync and async process errors, output capture, Lean command routing, and signal forwarding`.
- [x] `tools/artifact-conformance.js check` classified all fifteen official invalid modules, reported all twenty-five Talos and Wasmtime results, and passed with one warning for the exact six imported-memory failures.

## 2026-08-02: Complete Aggregate Artifact Gate

`tools/artifact-proof.js check-all` passed all twenty registered artifacts under the standard `tools/leanrun` resource policy.  The command checked each frozen file's SHA-256, length, package identity, and equality with its embedded Lean byte value, then built every decode, validation, exact translation, artifact-correctness, and behavioral target.  The final generated declaration module checked every theorem name recorded by the manifests and reported `Aggregate artifact proof passed: 20 artifacts`.

The LEB128 proof reached this result after division into reusable positive and negative iteration, completion, allocation, and prefix lemmas.  `Project.LebU32.NegFreshAlloc` states the exact fresh-allocation header writes and allocation prelude with an arbitrary postcondition, while `NegAfterFree`, `NegPrefix`, `NegIter`, and `Main` compose those results at the generated instruction boundaries.  The aggregate then passed every CLOB target; the largest measured modules were `Project.ClobCancel.Spec` at 1,092 seconds, `Project.ClobMatchFuel.FindBest` at 696 seconds, and `Project.ClobMatchFuel.Helpers` at 384 seconds.

The artifact driver now uses the shared asynchronous process helper instead of blocking in `spawnSync`.  The helper starts each child in a process group, forwards `SIGINT` and `SIGTERM`, waits for the child to close, and prevents an interrupted Node driver from leaving its runner, Lake process, or Lean child behind.  The focused process test confirmed that `SIGTERM` reaches a grandchild, and `tools/artifact-proof.js check-artifacts` then passed all twenty exact artifact targets through the revised command path.

Checks run:

- [x] `tools/artifact-proof.js check-all` returned `Aggregate artifact proof passed: 20 artifacts`.
- [x] `node --check tools/run-process.js`
- [x] `node --check tools/artifact-proof.js`
- [x] `node --check test/run_process.js`
- [x] `node test/run_process.js` returned `checked sync and async process errors, output capture, Lean command routing, and signal forwarding`.
- [x] `tools/artifact-proof.js check-artifacts` returned `Aggregate artifact theorem pass completed: 20 artifacts` through the signal-aware driver.

## 2026-08-01: Binary Decoder Soundness

The binary proof now defines exact cursor consumption and proves soundness for fixed bytes, bounded parsers, vectors, names, unsigned and signed LEB128, every accepted instruction, expressions, code bodies, sections, and complete modules.  The independent grammar now requires strict section ordering and uniqueness through increasing section ranks.  The theorem `Wasm.Binary.Proof.decode_sound` proves that every successful `decode` result satisfies `Grammar.Encodes` for the complete input `ByteArray`.

The section-loop proof tracks bytes consumed by each section, agreement between assigned fields and the final module, and preservation of empty fields for absent sections.  The decoder uses named opcode classification and a named section-step parser so the execution proof composes at stable parser boundaries.  `tools/leanrun --timeout 300 lake -d proofs/talos/lean env lean proofs/talos/lean/Project/Artifact/Binary/Proof/Decode.lean` completed successfully under the shared cgroup and machine-wide Lean lock.

## 2026-08-01: Artifact Decoder, Validator, and Talos Translation

The artifact-verification implementation now has a repository-owned raw WebAssembly syntax, bounded byte cursor, unsigned and signed LEB128 parsers, UTF-8 name parser, structured instruction decoder, restricted module decoder, executable validator, and Talos translation.  The accepted profile covers the type, function, memory, global, export, and code sections and every opcode emitted by the current compiler artifacts.  `docs/artifact-format.md` records the profile, trusted base, raw representation, package layout, and manifest fields against the WebAssembly Core 3.0 binary and validation specifications.

All twenty current `.generated` binaries decode, validate, and translate in one Lean process under `tools/leanrun`.  A separate comparison imports the twenty WAT-derived Talos caches and matches every translated module on functions, types, function exports, memory, and globals.  Focused primitive, corruption, and invalid-module tests cover LEB width boundaries, permitted overlong forms, truncation, trailing bytes, invalid UTF-8, section errors, type-index errors, memory limits, stack underflow, branch depth, local indices, immutable globals, alignment, and duplicate exports.

`Project.Artifact.Binary.Grammar` defines an independent declarative grammar over byte lists, including non-canonical LEB encodings permitted by the specification.  Decoder soundness against that grammar and validator soundness against an independent `CoreValid` relation remain unproved, so the current executable results do not constitute artifact-level verification.  The permanent decoder location in a pinned Talos fork and the Lean kernel build also remain unresolved design gates.

The GCD pilot embeds all 1,249 artifact bytes and records SHA-256 `51801200954786e42d28caf3ba8806d613ab31ec4abe9b5d4b672e28d953b3ae`.  Its generated raw cache builds separately, and a generic evidence lemma turns a successful computed `verifiedModule?` certificate into explicit decode and validation witnesses.  The GCD artifact target builds through this boundary, while its Boolean raw-cache comparison remains a test until a proved equality procedure or grammar-unambiguity theorem connects that result to propositional equality.

Whole-module kernel reduction does not provide a usable cache-equality boundary.  A direct theorem combining decode, validation, translation, and equality with `Project.Gcd.Program.module` reached a 300-second no-diagnostic timeout, a function-level theorem that still unfolded the whole decoder reached a 180-second no-diagnostic timeout, and isolated `decode artifactBytes = .ok cachedRaw` reached a 300-second no-diagnostic timeout.  The next proof work must use compositional parser soundness, grammar unambiguity, and small generated certificates rather than rerunning any of those unchanged terms.

The PairFree proof division produced a stable `Project.PairFree.BuildCore` target that built in 19 seconds.  `Project.PairFree.BuildTail` first produced a final-store bound diagnostic after 276 seconds, then reached a 360-second no-diagnostic timeout after that bound was added.  A smaller allocation-prefix probe also reached a 300-second no-diagnostic timeout, so the unchanged proof slices must remain unrun until another reusable lemma or module boundary reduces elaboration.

Checks run:

- [x] `tools/leanrun --timeout 180 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.PrimitivesTests`
- [x] `tools/leanrun --timeout 180 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.DecodeTests`
- [x] `tools/leanrun --timeout 180 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.ValidateTests`
- [x] One `ValidateFile` run decoded and validated all twenty current artifacts.
- [x] One `TranslateFile` run decoded, validated, and translated all twenty current artifacts.
- [x] One `CompareCaches` run returned `matched` for all twenty current WAT-derived Talos caches.
- [x] `tools/leanrun --timeout 240 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.Grammar`
- [x] `tools/leanrun --timeout 120 lake --dir proofs/talos/lean --no-ansi build Project.Artifact.Binary.Evidence`
- [x] `tools/leanrun --timeout 120 lake --dir proofs/talos/lean --no-ansi build Project.Gcd.Artifact`

## 2026-06-19: Talos Proof for Generated GCD WASM

`LeanExe.Examples.TalosGcd.gcd` is a small Euclidean GCD program written in the supported Lean subset.  The LeanExe compiler emits the WASM artifact stored at `proofs/talos/rust/build/gcd/program.wasm`; `wasm-tools print` produces the WAT that Talos decodes into `Project.Gcd.Program`.  The proof in `proofs/talos/lean/Project/Gcd/Spec.lean` states that exported function `0` terminates for all `UInt64` inputs and returns `UInt64.ofNat (Nat.gcd a.toNat b.toNat)`.

The proof follows the generated WASM, including the compiler’s Boolean-normalization blocks, rather than a hand-written WAT model.  Its loop invariant names the generated local frame, treats WASM locals `4` and `5` as the Euclidean state, leaves scratch locals unconstrained, and uses `y.toNat` as the decreasing measure.  The generated module includes LeanExe runtime exports, but the `gcd` export itself does not touch memory or call runtime functions, so the spec is store-parametric.

`tools/check-talos-gcd.sh` is the integrity check for this proof slice.  It rebuilds the Lean source with `lean-wasm`, emits a fresh WASM file, prints fresh WAT with `wasm-tools`, compares both files against the Talos proof inputs, and then rebuilds the Talos Lean proof project.  The script accepts `WASM_TOOLS` or finds `$HOME/.cargo/bin/wasm-tools`, because `cargo install` does not guarantee the binary is on the noninteractive shell path.

Checks run:

- [x] `bash tools/check-talos-gcd.sh` rebuilt `LeanExe.Examples.TalosGcd`, compared regenerated WASM and WAT against `proofs/talos/rust/build/gcd/`, and built the Talos proof project.
- [x] `build/tools/wasmtime/current/wasmtime --invoke gcd proofs/talos/rust/build/gcd/program.wasm 48 18` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke gcd proofs/talos/rust/build/gcd/program.wasm 270 192` returned `6`.
- [x] `build/tools/wasmtime/current/wasmtime --invoke gcd proofs/talos/rust/build/gcd/program.wasm 17 0` returned `17`.

## 2026-06-16: Helper Result Owner Aliases

The orderbook WASM harness exposed a release-analysis bug in functions that return heap-bearing structures assembled from helper results.  The reduced case was a depth state with `bids` and `asks` arrays: the recursive helper returned one accumulator array unchanged, while the caller copied the helper result into a `DepthResult` and then released the original empty array local.  Rendering the returned result then read a freed empty array; empty stdin produced corrupt depth output, and non-empty stdin trapped in Wasmtime.

Release analysis now expands returned owner slots through local lets and helper calls before deciding which non-recursive owned temporaries can be released.  A helper call contributes its argument slots to that expansion only when the helper has heap parameters and at least one heap result owner that the existing fresh-result summary does not prove fresh.  This keeps the existing release behavior for helpers that return newly allocated arrays or byte arrays, while preserving argument-owned roots returned through accumulator helpers.

The new `depthAliasRun` WASI example in `LeanExe.Examples.Correctness` keeps the failing shape without importing the orderbook module.  It selects a bid-only or ask-only book from stdin, computes old-style depth through a two-array state, and renders both sides into `ByteArray`.  Before the fix, empty stdin emitted the corrupt sequence beginning `0 1 12 6 48 5501223100278326855`, and stdin `x` trapped at `wasm unreachable`; after the fix, the outputs are `0 1 12 6 0\n` and `0 0 1 100 6\n`.

Checks run:

- [x] `lake build LeanExe.Extract.Values`
- [x] `lake build lean-wasm`
- [x] `.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 16 --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.depthAliasRun --out .lake/build/wasi-programs/depthAliasRun.final.wasm`
- [x] `timeout 5s build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/depthAliasRun.final.wasm < /dev/null` returned `0 1 12 6 0`.
- [x] `printf x | timeout 5s build/tools/wasmtime/current/wasmtime run .lake/build/wasi-programs/depthAliasRun.final.wasm` returned `0 0 1 100 6`.
- [x] `node test/wasi_program.js` returned `checked 35 WASI program cases, 2 traps, and 7 rejections`.
- [x] `node test/refcount.js` returned `checked 38 refcount cases`.
- [x] `node test/ownership_report.js` returned `checked 8 ownership report cases`.
- [x] `node test/core_correctness.js` returned `checked 784 accepted, 34 rejected, and 13 trapped cases`.
- [x] In `orderbook-wasm`, `lake env ../leanexe/.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 16 --module PmobOrderBook.LeanExeDepthRenderRepro --entry PmobOrderBook.LeanExeDepthRenderRepro.run --out .lake/build/repro-depth-old-state.fixed.wasm`, followed by empty stdin and stdin `x` Wasmtime runs, returned `0 1 12 6 0` and `0 0 1 100 6`.
- [x] In `orderbook-wasm`, `lake env ../leanexe/.lake/build/bin/lean-wasm ownership-report --module PmobOrderBook.LeanExeDepthRenderRepro --entry PmobOrderBook.LeanExeDepthRenderRepro.run` showed `PmobOrderBook.LeanExeDepthRenderRepro.oldDepth` with `compiler statement releases: none`.
- [x] In `orderbook-wasm`, `lake env ../leanexe/.lake/build/bin/lean-wasm compile-wasi-stdin-except --max-input-bytes 4096 --module PmobOrderBook.RawCommand --entry PmobOrderBook.RawCommand.run --out .lake/build/pmob-orderbook-raw.wasm`
- [x] In `orderbook-wasm`, `lake env lean PmobOrderBook/KernelTest.lean`
- [x] In `orderbook-wasm`, `lake env lean PmobOrderBook/RawCommandTest.lean`
- [x] In `orderbook-wasm`, `lake env lean PmobOrderBook/LeanExeDepthRenderReproTest.lean`
- [x] In `orderbook-wasm`, `go test -count=1 ./harness` returned `ok  	leanclob/orderbookwasm/harness	5.232s`.

## 2026-06-16: Type-Class Specialization Through List Helpers

Type-class evidence specialization now feeds the expression-level structural-recursion discovery pass.  When a same-root helper call has static class evidence and concrete supported runtime arguments, the discovery pass inline-specializes the helper body, normalizes class evidence, and collects any structural-recursion helpers exposed by the specialized body.  This lets generic class-constrained helpers compile when their specialized bodies call `List.foldl` or `List.find?` over supported element layouts.

The new correctness examples use `TypeclassScore` over `List (Option UInt64)`.  `typeclassScoreListFoldlDemo` folds scores through `List.foldl`, and `typeclassScoreListFindDemo` searches with `List.find?` before scoring the returned value.  Direct `List.any` remains covered by existing closed-predicate tests, but the generic class-constrained `List.any` shape still needs a predicate-extraction improvement.

Checks run:

- [x] `lake build LeanExe.Extract.Core LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/report_classification.js`
- [x] `node test/run_all.js` returned `checked 114 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 784 accepted, 34 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 298 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-28: Type-Class Boundary Hardening

Type-class diagnostics now distinguish public runtime evidence from internal evidence-bearing helpers.  Public entries with unresolved class evidence or explicit dictionary parameters reject with `runtime class evidence is not supported`, while the report command describes internal class methods, instances, and class constructors as static-specialization requirements.  The report remains entry-aware, so accepted concrete wrappers can mention class declarations in their dependency graph without marking the whole reachable graph as rejected.

Evidence normalization now runs at class-method application sites that reach extraction after specialization, which lets source-defined class methods compile inside additional direct-lambda array callbacks.  The correctness examples now compare `TypeclassScore` methods inside `Array.any` and `Array.find?`, in addition to the earlier `Array.foldl` case.  The BEq path keeps custom lambda instances on the normalization path, but it preserves the existing structural equality lowering for evidence that is structurally derived or built from `instBEqOfDecidableEq`, including `Option.instBEq` and `Array.instBEq`.

This pass also filled direct fixed-width primitive gaps exposed by the stricter evidence handling.  Direct `UInt64`, `UInt32`, and `UInt8` comparison methods lower as conditions, direct `UInt64`, `UInt32`, and `UInt8` complement methods lower without relying on class projection unfolding, and direct `UInt8.land`, `UInt8.lor`, and `UInt8.xor` now share the existing fixed-width bitwise lowering.  Numeric class projections already handled by primitive extraction stay on that explicit path instead of being unfolded through library instance bodies.

Checks run:

- [x] `lake build LeanExe.Extract.Core lean-wasm`
- [x] `lake build LeanExe.Extract.Report lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness lean-wasm`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node --check test/report_classification.js`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreArrayAnyDemo --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreArrayAnyDemo`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassScoreArrayFindDemo --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassScoreArrayFindDemo`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectTypeclassEntry --out .lake/build/typeclass-reject-entry.wasm` rejected with `runtime class evidence is not supported: LeanExe.Examples.Correctness.rejectTypeclassEntry`.
- [x] `.lake/build/bin/lean-wasm compile --module LeanExe.Examples.Correctness --entry LeanExe.Examples.Correctness.rejectTypeclassRuntimeDictionaryParam --out .lake/build/typeclass-reject-dict.wasm` rejected with `runtime class evidence is not supported: LeanExe.Examples.Correctness.rejectTypeclassRuntimeDictionaryParam`.
- [x] `node tools/compare-standard.js --self-test` returned `checked 296 standard Lean comparison cases`.
- [x] `node test/core_correctness.js` returned `checked 782 accepted, 34 rejected, and 13 trapped cases`.
- [x] `node test/bytearray_alloc.js` returned `checked 70 bytearray allocation cases`.
- [x] `node test/report_classification.js` returned `checked 113 report classification cases`.
- [x] `node test/run_all.js` returned `checked 113 report classification cases`, `checked 8 ownership report cases`, `checked JavaScript WASM execution guard`, `checked 782 accepted, 34 rejected, and 13 trapped cases`, `checked 38 refcount cases`, `checked 70 bytearray allocation cases`, `checked 23 asciistring cases`, `checked 4 intmap cases`, `checked 48 json program cases`, `checked 35 WASI program cases, 2 traps, and 7 rejections`, `checked 296 standard Lean comparison cases`, and `checked 56 cases`.

## 2026-05-28: Static Type-Class Evidence

LeanExe now treats class evidence as a static specialization input for inline-specialized helpers.  The classifier reads Lean's imported class-extension entries directly instead of importing modules with `loadExts := true`, which preserves access to source-defined classes without requiring imported initializer execution in the `lean-wasm` executable.  Specialized helper bodies run through bounded evidence normalization that beta-reduces, unfolds class evidence applications, unfolds class projection functions, and reduces projections from class constructors before ordinary extraction.

The correctness examples cover `BEq`, `Inhabited`, and a source-defined `TypeclassScore` class.  The custom `BEq` example is intentionally nonstructural, so it catches the unsound path where generic `==` would ignore the selected instance and lower to structural equality.  The `TypeclassScore` examples cover scalar and structure instances, a dependent `Option` instance, and a class method used inside an `Array.foldl` direct lambda.  Runtime dictionaries, exported unresolved class constraints, dynamic dispatch, and unsupported method result types remain outside the accepted subset.

The implementation also adds direct lowering for `UInt64`, `UInt32`, and `UInt8` arithmetic primitives exposed after method inlining, plus proof-erased lowering for `UInt64.ofNatLT`, `UInt32.ofNatLT`, and `UInt8.ofNatLT`.  Those forms are not type-class-specific; they are ordinary checked Lean fixed-width integer operations that became visible once evidence normalization exposed method bodies.  The `ofNatLT` match uses plain `Name` values because quoting the external declaration in the compiled extractor made the native `lean-wasm` executable look for a nonexistent runtime implementation of that checked constructor.

Checks run:

- [x] `lake build LeanExe.Extract.Types LeanExe.Extract.Core lean-wasm`
- [x] `lake build LeanExe.Examples.Correctness`
- [x] `node --check tools/compare-standard.js`
- [x] `node --check test/core_correctness.js`
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassSameUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassSameUInt64`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassSameCustomBEq --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.Examples.Correctness.typeclassSameCustomBEq`.
- [x] `node tools/compare-standard.js --mode pure --module LeanExe.Examples.Correctness --entry typeclassDefaultUInt64 --result-slots '#[__leanexeValue]'` returned `matched pure LeanExe.E