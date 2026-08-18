# Bounded wrapping-sum artifact walkthrough

## Summary

This demo accepts an `Array UInt64`.  An input containing at most eight elements returns a singleton array whose element is the wrapping sum of the input.  A longer input returns an empty array.

The 1,979-byte WASM module has SHA-256 digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  Its valid branch allocates a singleton result and traverses the input with an emitted loop, while its invalid branch allocates an empty result.  Independent `leanexegen verify -s` accepted the complete package and exact artifact theorem.

The retained root proof completed Stage 5 in 2,082.889 seconds and contained 508 lines.  The fastest retained run completed Stage 5 in 1,638.250 seconds, but its agent rejected the learned theorem supplied by that run's forest.  The later setup-frame reproof took 1,780.162240 seconds and produced a 543-line proof, so the demo reports time, source structure, retrieval, and theorem use separately.

## Program and specification

The [generation request](request.txt) fixes the public behavior, the maximum input length, and wrapping `UInt64` addition.  The [formal specification](spec.lean) defines the expected array and the branch-sensitive heap reserve required by the artifact theorem.  The [generated Lean program](program.lean) expresses the valid result with `Array.foldl`.

```lean
def compute (input : Array UInt64) : Array UInt64 :=
  if input.size ≤ 8 then
    #[input.foldl (fun sum element => sum + element) 0]
  else
    #[]
```

The [WASM module](program.wasm) is the executable covered by the theorem.  The [WAT rendering](program.wat) exposes the emitted length test, two fixed-array allocator paths, indexed input loads, wrapping accumulator update, and result stores.  The theorem refers to the exact module bytes rather than the Lean source or compiler.

## Artifact proof

The [compiler annotations](program.annotations.json) identify the bounded array-length dispatch and the nested array-fold region.  The [annotation equality](annotation-matches.lean) names the decoded fold interval at instructions 39 through 65 of the valid branch, its setup interval through instruction 62, the 16-instruction continuing guard-and-load prefix, and the accumulator-to-result transfer at instructions 63 through 65.  It also identifies the complete constant-capacity prefix at the start of each length branch.  Lean proves all six equalities by reduction, while the consumer checks the reported branch arithmetic, accumulator, item, index, effective-stop, staging, scratch, guard, element-address load, back-edge, and result-local roles against the decoded artifact.

The [proof recipe plan](proof-recipes.json) names `FixedArrayLengthDispatch.leProgram_spec`, both capacity equalities, all four fold-program equalities, `FixedArrayCapacity.constantProgram_spec`, `FixedArrayFold.forwardSetupProgram_spec`, both traversal-guard edge theorems, `FixedArrayFold.resultProgram_spec`, the frame-projection declarations, and the generic fold-prefix declarations.  The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) provide the structured LTG catalog, allocator guidance, array-framing guidance, and fold invariant.  The retained measured proof predates the capacity and exit declarations; it retrieved the earlier entries from its archived task-specific LTG view and used each of the three fold subregion theorems.

The [behavioral proof](proof.lean) uses `ArrayFold.foldPrefix` as the loop-carried mathematical coordinate.  It applies the checked fold-setup theorem before the invariant, the traversal theorem in the continuing case, `foldPrefix_succ` at the back edge, and the checked result-placement theorem after exit.  The proof also applies the shifted allocator theorem, length-store theorem, payload-store theorem, and final array-representation theorems to the exact decoded program.

The [proof journal](proof-journal.md) records the successful path and each rejected intermediate reduction.  Structured retrieval selected the generic dispatch, fold, traversal, result, allocation, and memory entries while excluding artifact-specific worked examples.  Its capacity-prefix and local-projection gaps led to `FixedArrayCapacity.constantProgram_spec` and the two `Frame` projection theorems, which the current package catalogs without changing the measured proof or artifact.

The [proof telemetry](proof-telemetry.json), [timing comparison](proof-timings.json), and [stage reports](stage-reports.json) preserve time intervals and source identities.  The retained proof has 508 lines, 2,155 whitespace-delimited words, and 24,327 bytes, compared with 416 lines, 1,848 words, and 17,797 bytes in the preceding annotation run.  Its 34.7-percent time reduction accompanies a 22.1-percent line increase, so the result supports faster proof generation and better shared-boundary use while recording a proof-size cost for the next LTG iteration.

## Capacity and frame comparison

The [current accepted comparison package](experiments/capacity-frame-current.proof/) holds the specification, source, and WASM fixed while adding exact capacity-prefix equalities, `FixedArrayCapacity.constantProgram_spec`, and the structured LTG.  Independent verification accepted its artifact theorem under the current proof-kit identity; the [original generation package](experiments/capacity-frame.proof/) preserves the proof kit supplied during generation.  Its monotonic Stage 5 measurement was 3,070.994 seconds, 47.4 percent slower than the retained fold-structure proof, while remaining 3.7 percent faster than the earlier fold-annotation proof and 10.5 percent faster than the baseline.

The comparison proof contains 642 lines, 2,524 words, and 30,858 bytes.  It uses the shared capacity theorem in both length branches and reaches the checked setup, traversal, result-placement, allocator, and result-store boundaries, but it adds local theorems for the traversal exit edge, the accumulator/index update, and two getters from the updated frame.  The exit edge and final root transfer have since become checked ProofKit theorems, and traversal guidance now names the shared combined-to-internal frame projection; the accumulator/index update remains a candidate compiler motif rather than a promoted general theorem.

The telemetry's UTC timestamps span 12,764.900 seconds, while its monotonic Stage 5 measurement records 3,070.994 seconds.  The 9,693.906-second difference occurred outside the monotonic interval, and the accessible system journal did not identify its cause.  Timing comparisons therefore use the telemetry's monotonic total, while `proof-timings.json` preserves both measurements.

## Compact fold-boundary comparison

The [compact-boundary package](experiments/compact-fold-boundary.proof/) tests the shared traversal-exit and final-transfer theorems together with an artifact-local, continuation-generic theorem for the post-load accumulator and index update.  Direct simplification of that update under the complete loop continuation exhausted one million heartbeats, while the compact theorem checked the instruction tail against a named frame and let the outer proof establish its invariant separately.  Independent package verification accepted the exact artifact theorem.

Stage 5 took 2,297.877 seconds, including 2,251.334 seconds in Codex and 35.168 seconds in outer acceptance.  The result is 10.3 percent slower than the retained fold-structure proof, 25.2 percent faster than the capacity-and-frame screen, and 33.0 percent faster than baseline.  Its 655-line, 2,472-word, 32,143-byte proof is 147 lines longer than the retained proof because the update boundary and three frame getters remain artifact-local.

The experiment establishes that a compact semantic endpoint can prevent heartbeat exhaustion and complete the proof.  It does not establish a proof-time or proof-size improvement over the retained primary proof, so the retained package remains primary.  [Artifact Proving](../../docs/artifact-proving.md) records the current abstraction, measurement, and evidence rules.

## Compiler-described guarded-back-edge comparison

The [guarded-back-edge package](experiments/guarded-back-edge.proof/) replaces the artifact-local update theorem with a generic compiled ProofKit theorem.  The compiler annotation supplies a versioned scalar descriptor for the fold body and done condition, while the annotation consumer proves that nested loop instructions 16 through 37 equal the generic guarded-back-edge program.  The generated recipe and structured LTG expose that equality, the body and condition evaluator theorems, and `ScalarTransition.guardedBackEdgeProgram_spec` to the proving agent.

The fresh agent selected `guarded-back-edge` on its first structural search and applied the theorem after the checked traversal prefix.  The theorem discharged the wrapping-add body, done condition, successor prefix invariant, and strict remaining-input measure without reducing the WAT update beneath the outer loop postcondition.  Generic evaluation of the continuing index assignment exceeded the simplifier step limit, after which `Stmt.eval_toState` and a finite `U64State` reduction closed the remaining descriptor obligation.

Stage 5 took 1,972.223 seconds, including 1,872.127 seconds in Codex and 79.123 seconds in outer acceptance.  The run is 5.3 percent faster than the retained 2,082.889-second primary and 14.2 percent faster than the local compact-boundary experiment.  Its 589-line, 2,208-word, 31,148-byte proof is 15.9 percent longer than the primary but 10.1 percent shorter than the local compact-boundary proof, and a separate `leanexegen verify -s` run accepted the package.

This single measurement supports theorem applicability, structured retrieval, and a modest proof-time reduction.  Demo 10 later applied the descriptor boundary to wrapping multiplication without multiplication-specific ProofKit support, while Demo 11 applied the resulting fold-body interface to bitwise XOR.  The retained root package remains the shorter primary because those cross-operation results establish applicability without producing a smaller Demo 9 proof.

## Fold-body composition capability

The [fold-body composition package](experiments/fold-body-composition.proof/) applies the current annotation generator and proof kit to the unchanged Demo 9 artifact.  Its generated recipe supplies the checked continuing-loaded-frame equality and `FixedArrayFoldBody.continuingGuardedProgram_spec`, and independent package verification accepts the exact artifact theorem.  The archived behavioral proof predates the composition theorem, so this package establishes annotation recognition, theorem availability, and package integrity rather than proof-agent retrieval or use; the fresh fixed-artifact reproof measures those claims separately.

## Fold-body composition reproof

The [fresh fold-body reproof](experiments/fold-body-reproof.proof/) selected `fixed-array-fold-body` in its first annotation-driven catalog query and applied `FixedArrayFoldBody.continuingGuardedProgram_spec` to the wrapping-add loop.  The theorem consumed the checked indexed load, generated loaded-frame equality, wrapping-add body evaluator, false done condition, index-increment evaluator, and guarded back edge.  The artifact proof retained the sum-prefix successor equation, invariant reconstruction, and decreasing measure, and a separate `leanexegen verify -s` run accepted the complete package over the unchanged digest.

Stage 5 took 2,074.169 seconds, including 1,984.791 seconds in Codex and 69.416 seconds in outer acceptance.  The run was 8.720 seconds, or 0.4 percent, faster than the 2,082.889-second retained fold-structure proof, 101.946 seconds, or 5.2 percent, slower than the guarded-back-edge screen, and 223.708 seconds, or 9.7 percent, faster than the local compact-boundary screen.  These results establish no proof-time improvement over the theorem's immediate component, but they establish fresh selection and accepted use across wrapping addition and multiplication.

The proof contains 588 lines, 2,484 whitespace-delimited words, and 29,973 bytes.  Compared with the guarded-back-edge proof, it has one fewer line, 276 more words, and 1,175 fewer bytes, so the proof-size evidence is mixed.  The journal also records repeated proof-local frame projections before the singleton suffix and the need to fix the theorem's module, environment, store, and frame arguments when callback inference generalizes them; the structured guidance records both findings, while the shorter root proof remains primary.

## Generated frame-accessor substitution

The [frame-accessor package](experiments/frame-accessors.proof/) applies a current annotation pass to the unchanged Demo 9 artifact.  The annotation module proves the continuing frame's exact parameter list, internal-local length, empty operand stack, and value at every combined parameter-and-local index.  Its recipe advertises those declarations together with the shared `FixedArrayFold.resultFrame_get_result` and `resultFrame_get_of_ne` theorems.

The manual substitution removed ten proof-local `rfl` projection theorems from the fresh fold-body proof.  At each traversal or suffix boundary, restricted simplification unfolds the semantic `foldFrame` abbreviation and applies one generated accessor, while the shared result-frame theorems establish the written result and preserved root.  A separate `leanexegen verify -s` run accepted the complete artifact theorem over digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.

The proof decreased from 588 to 555 lines, from 2,484 to 2,084 whitespace-delimited words, and from 29,973 to 29,291 bytes.  The compiler-generated annotation module grew because it contains one exact theorem per frame slot, and the proof uses long declaration names, so line and word reductions better describe the removed local reasoning than raw bytes.  This manual substitution has no proof-generation timing and makes no time claim; a fresh fixed-artifact run would measure agent retrieval and construction separately.

## Fresh frame-accessor reproof

The [fresh frame-accessor reproof](experiments/frame-accessor-reproof.proof/) began from the same specification, source, WASM bytes, annotation package, and structured LTG supplied to the manual substitution.  Its second annotation-directed catalog query found `annotated-fold-frame-accessors`, and the accepted proof uses the generated parameter, local-length, value-stack, and combined-local getter theorems.  It also applies `FixedArrayFold.resultFrame_get_result` and `resultFrame_get_of_ne`, and it declares no proof-local frame-projection theorem.

Stage 5 took 2,230.869 seconds, including 2,173.264 seconds in Codex and 39.702 seconds in outer acceptance.  The run was 7.6 percent slower than the 2,074.169-second fold-body reproof and 13.1 percent slower than the 1,972.223-second guarded-back-edge screen.  Its proof contains 616 lines, 2,541 whitespace-delimited words, and 30,901 bytes, compared with 588 lines, 2,484 words, and 29,973 bytes for the earlier fold-body reproof.

The telemetry's UTC timestamps span 4,843.670 seconds, which exceeds the monotonic Stage 5 duration by 2,612.801 seconds.  Timing comparisons use the monotonic measurement, as they do for earlier runs with UTC-to-monotonic differences.  The preserved telemetry records both timestamps and the component durations.

The journal records seventeen edited import-check candidates inside one accepted Codex task.  The generated accessors removed the recurring task of proving exact frame projections, but the agent spent most revisions composing dispatch, allocation, loop initialization, result construction, and dependent fold-body premises.  The result supplies fresh retrieval and theorem-use evidence while recording adverse proof-time and source-size measurements.

Independent `leanexegen verify -s` accepted the preserved package over digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  The earlier manual substitution remains the smaller source comparison, and the retained root package remains the primary timing and size reference.  Demo 10 subsequently tested the same accessor interface on wrapping multiplication, and Demo 11 used it on bitwise XOR.

## Fold-completion adapter experiment

The [fold-completion package](experiments/fold-completion.proof/) checks the generated `function_0_array_fold_0_singleton_result_spec` theorem against the unchanged wrapping-sum artifact.  The [manual proof](experiments/manual-fold-completion.lean) applies that theorem to the compact singleton-result postcondition, replacing the explicit local-layout, accumulator-transfer, root-preservation, result-placement, and final-local validity obligations.  The sum-prefix invariant and represented singleton result remain in the artifact proof.

Independent `leanexegen verify -s` accepted the complete package and exact artifact digest.  The proof decreased from 616 to 569 lines, from 2,541 to 2,404 whitespace-delimited words, and from 30,901 to 28,245 bytes.  Demo 11 applies the same operation-independent interface directly to a public XOR-branch postcondition.

This manual substitution provides no proof-generation-time measurement.  The package omits the predecessor proof's telemetry because those timings belong to a different source.  The fresh fold-completion reproof below records the corresponding structured retrieval and proof-construction measurement.

## Fresh fold-completion reproof

The [fresh fold-completion reproof](experiments/fold-completion-reproof.proof/) began from the unchanged specification, Lean source, annotations, and 1,979-byte WASM artifact.  Its first structured searches selected `compact-loop-suffix-boundary`, `fixed-array-fold-body`, the fold-frame accessors, and the related generic fold entries.  The accepted proof applies the generated `function_0_array_fold_0_singleton_result_spec` theorem directly, with no proof-local singleton-result theorem or postcondition bridge.

Stage 5 took 1,992.546 seconds, including 1,922.343 seconds in Codex and 54.378 seconds in outer acceptance.  The run was 238.323 seconds, or 10.7 percent, faster than the 2,230.869-second frame-accessor screen and 90.343 seconds, or 4.3 percent, faster than the retained 2,082.889-second fold-structure proof.  It was 20.323 seconds, or 1.0 percent, slower than the 1,972.223-second guarded-back-edge screen, so the timing evidence does not establish a new best result.

The proof contains 526 lines, 2,039 whitespace-delimited words, and 28,132 bytes.  Relative to the frame-accessor screen, it removes 90 lines and 502 words; relative to the manual fold-completion proof, it removes 43 lines and 365 words.  Separate `leanexegen verify -s` accepted the package over the unchanged artifact digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.

The journal records fourteen successful import-check and Lean-build cycles from the starter through final acceptance.  The completion adapter closed the complete loop-exit suffix on its first application, while most remaining work concerned capacity and allocator frame projections, loop-invariant construction, and the strict-index body.  The annotations identified local 18 as `releaseReadyLocal`, which let the agent repair the final invariant, but they supply no generated accessor for that loop-carried value and no capacity-frame or allocator-root getter family.  Those gaps define the next general interface review.

## Capacity-to-allocation composition reproof

The [capacity-to-allocation reproof](experiments/capacity-allocation-reproof.proof/) preserves the specification, source, annotations, 1,979-byte WASM artifact, and artifact digest from the earlier controlled runs.  Its structured LTG search selected `FixedArrayAllocatorWindow.constantCapacityRegion_spec_withTail`, then applied the theorem to the length-one valid branch and the length-zero invalid branch.  The theorem executes each constant-capacity prefix together with the immediately following shifted allocator and supplies the normalized minimum-capacity fact needed by the allocator proof.

The agent again selected `wp_fixed_array_length_le_dispatch_from` and `wp_block_loop` from their structured tactic records.  It reached the fold continuation that the preceding corrected screen never reached, used `afterContinue.toState.toLocals []` as the callback frame, and closed the successor invariant and decreasing measure.  It also used the generated singleton-result adapter, exact frame accessors, scalar evaluator equations, and shared fold-prefix theorems before the outer checker and a separate `leanexegen verify -s` run accepted the complete package.

Stage 5 took 1,759.087 seconds, including 1,686.337 seconds in Codex and 45.688 seconds in outer acceptance.  The result is 233.459 seconds, or 11.7 percent, faster than the fresh fold-completion reproof and 213.136 seconds, or 10.8 percent, faster than the guarded-back-edge screen.  A later stateful run took 1,638.250 seconds but rejected its learned theorem, so neither single measurement isolates the capacity-to-allocation composition theorem from agent and machine variation.

The accepted source contains 584 lines, 2,269 whitespace-delimited words, and 30,369 bytes, compared with 526 lines, 2,039 words, and 28,132 bytes for the fresh fold-completion proof.  The [manual capacity-to-allocation proof](experiments/manual-capacity-allocation.lean) applies the same theorem to that predecessor and contains 498 lines, 1,975 words, and 26,131 bytes.  The contrast shows that the theorem presents a compact checked interface, while the fresh agent's full branch and loop construction still determines the resulting proof size.

## Generated setup-frame reproof

The [setup-frame reproof](experiments/setup-frame-reproof.proof/) preserves the specification, source, and WASM digest `aa263bbfa89c333f9fab497f1a2c370f476afc3419015d17b368cb7c8a6086d5`.  Its archived forest contains `leanexe-core` and `proposal-4f56fd45fe24-d4f7d73b3648`.  The agent found `function_0_array_fold_0_setup_frame_eq` in the generated recipe and applied it at line 200 of `Behavior.lean`.

The equality normalized `FixedArrayFold.forwardSetupFrame` to the generated continuing frame, after which Lean reached the folded loop without reducing the complete local-update chain.  The accepted proof records eleven used entries, including the proposal package's singleton-result theorem.  Independent `leanexegen verify -s` completed with exit status zero.

Stage 5 took 1,780.162240 seconds, including 1,648.772899 seconds in Codex and 95.521525 seconds in outer acceptance.  The 543-line, 2,320-word, 29,074-byte source has SHA-256 digest `6ed3450604a240e019b28f0bafcc27760b8fbdf7196a5e973abd17e9731b99ee`.  This run took 141.912 seconds longer but used 107 fewer lines than the 1,638.250-second, 650-line stateful run, and it took 21.075 seconds longer but used 41 fewer lines than the 1,759.087-second, 584-line capacity-to-allocation run.  These single-run comparisons do not isolate the effect of the setup-frame equality.

## Execution

The first sample exercises wrapping addition in the valid branch.  The second sample exceeds the maximum length and exercises the empty-result branch.  Direct execution of the proved artifact produced these values:

```text
Input: [18446744073709551615, 1]
Output: [0]
Input: [1, 2, 3, 4, 5, 6, 7, 8, 9]
Output: []
```

## Retained files

Every retained root file fixes a generation input, artifact, proof context, or measured result.  The [verification package](program.proof/) contains the complete embedded artifact, generated proof modules, filtered LTG snapshot, tool pins, and package manifest accepted by the independent verifier.  The table identifies each root file and the package directory.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The bounded wrapping-sum behavior supplied to leanexegen. |
| [Formal specification](spec.lean) | The expected result, runtime precondition, and artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation of the artifact. |
| [Behavioral proof](proof.lean) | The accepted proof using the shared fold and array support. |
| [Compiler annotations](program.annotations.json) | The checked bounded-length region emitted by the compiler. |
| [Annotation equality](annotation-matches.lean) | The generated equalities for both capacity prefixes and the complete fold, setup, continuing, and result intervals. |
| [Proof recipe plan](proof-recipes.json) | The length dispatch, capacities, fold invariant, exact subregions, frame projections, and checked execution declarations. |
| [Selected strategy notes](proof-strategies.md) | The feature-selected proof guidance supplied to the agent. |
| [Program feature report](proof-task-features.json) | The instruction, local, operation, annotation, and LTG feature inventory. |
| [Proof journal](proof-journal.md) | The agent's searches, failed checks, proof decisions, and final acceptance. |
| [Proof telemetry](proof-telemetry.json) | The measured Stage 5 intervals and accepted proof identity. |
| [Timing comparison](proof-timings.json) | The baseline and structured-LTG timing and proof-size measurements. |
| [Stage reports](stage-reports.json) | The accepted specification, source, and artifact-proof task reports. |
| [Verification package](program.proof/) | The self-contained package accepted by `leanexegen verify -s`. |
| [Current capacity and frame comparison](experiments/capacity-frame-current.proof/) | The slower structural comparison re-frozen and independently accepted under the current proof kit. |
| [Original capacity and frame generation](experiments/capacity-frame.proof/) | The same accepted proof with the proof-kit identity supplied during its measured generation. |
| [Compact fold-boundary comparison](experiments/compact-fold-boundary.proof/) | The accepted fixed-artifact proof that isolates the post-load update behind a compact continuation-generic theorem. |
| [Compiler-described guarded-back-edge comparison](experiments/guarded-back-edge.proof/) | The accepted fixed-artifact proof that uses the generic guarded-back-edge theorem with compiler-generated transition evidence. |
| [Fold-body composition capability](experiments/fold-body-composition.proof/) | The current annotations, proof kit, and accepted archived proof for the unchanged artifact; its behavioral proof predates the fold-body theorem. |
| [Fresh fold-body composition reproof](experiments/fold-body-reproof.proof/) | The independently verified fixed-artifact proof that retrieved and used the shared composition theorem for wrapping addition. |
| [Generated frame-accessor substitution](experiments/frame-accessors.proof/) | The independently verified manual proof that replaces ten local frame projections with exact generated accessors and shared result-frame getters. |
| [Fresh frame-accessor reproof](experiments/frame-accessor-reproof.proof/) | The independently verified fixed-artifact proof whose agent retrieved and used the generated accessors and shared result-frame getters. |
| [Fold-completion package](experiments/fold-completion.proof/) | The independently verified manual proof using the generated exact singleton-result adapter. |
| [Fresh fold-completion reproof](experiments/fold-completion-reproof.proof/) | The independently verified fixed-artifact proof that retrieved and applied the generated completion adapter. |
| [Capacity-to-allocation reproof](experiments/capacity-allocation-reproof.proof/) | The independently verified fixed-artifact proof that retrieved and applied the capacity-plus-allocator composition in both branches. |
| [Generated setup-frame reproof](experiments/setup-frame-reproof.proof/) | The independently verified fixed-artifact proof that retrieved and used the generated setup-frame equality and the selected proposal theorem. |
| [Manual capacity-to-allocation proof](experiments/manual-capacity-allocation.lean) | The checked source substitution that establishes the composed theorem's smaller proof interface without a generation-time measurement. |
| [Manual fold-completion proof](experiments/manual-fold-completion.lean) | The readable behavioral proof retained by the fold-completion package. |
