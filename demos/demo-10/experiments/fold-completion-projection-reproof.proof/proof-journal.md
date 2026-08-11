# Proof Journal

## 2026-08-11: Initial check and retrieval start

I ran the untouched candidate with `/home/somebody/src/leanexe/tools/leanrun --timeout 60m lake -d . --no-ansi build LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactResult`.  The build reached `Behavior.lean` and failed with the deterministic starter goal: after the `RuntimeReady` decomposition and common array facts, the remaining goal is the complete `TerminatesWith env module 0 initial [Value.i64 inputPtr]` postcondition.  The diagnostic confirms that proof construction must begin at function execution rather than repairing the starter decomposition.

I began LTG retrieval by opening `LTG/categories.json`.  Its `compiler-motifs`, `loops`, `arrays`, `allocation`, `memory`, and `proof-construction` indexes can describe the current goal, with the first three most likely to identify an exact composition.  I have not selected or rejected an entry yet because the category catalog contains summaries rather than theorem metadata.

## 2026-08-11: Exact recipe selection

I searched the `compiler-motifs`, `arrays`, and `proof-construction` indexes for `leanexe.array.length-dispatch.v1`, `FixedArrayLengthDispatch`, and `wp_fixed_array_length_le_dispatch_from`.  I also searched the `compiler-motifs`, `loops`, and `arrays` indexes for `leanexe.array.fold.v1`, `foldPrefix`, `guardedBackEdgeProgram_spec`, `wp_loop_cons`, and `FixedArrayFold`, then searched the `allocation`, `arrays`, and `memory` indexes for `singletonResultProgram_spec`, `constantProgram_spec`, and `capacityFrame`.  These queries identified the length-dispatch entry as the exact current boundary and identified fold, capacity, traversal, frame-accessor, and singleton-result entries for later branch goals.

I inspected `LTG/entries/fixed-array-length-dispatch/entry.json` and its `README.md`.  I selected this entry because `PROOF_RECIPES.json` gives the exact `leProgram_spec` invocation for local 7 and bound 8, while `AnnotationMatches.function_0_length_dispatch_0_function_eq` proves that `func0` has the required decoded decomposition.  I have not opened the other matching entries yet because their theorems apply only after dispatch exposes the valid or invalid branch.

`PROOF_RECIPES.json` contains two direct recipes and no complete composition.  I will first apply `Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl`, rewrite with `function_0_length_dispatch_0_function_eq`, and invoke `wp_fixed_array_length_le_dispatch_from hArray at 7, 8` exactly.  Progress means that Lean replaces the public execution goal with valid-size and invalid-size branch weakest-precondition obligations; a shape or frame failure would trigger another retrieval checkpoint.

## 2026-08-11: Dispatch recipe shape diagnostic

The import check accepted the first edit, while the Lean build failed before the dispatch theorem.  `of_wp_entry_for` left the program displayed as `func0Def.body`, so rewriting with a theorem whose left side is `func0` found no syntactic occurrence.  This is a local definitional-shape issue rather than a worse proof boundary, because the goal remains the body-level `wp` required by the selected entry.

The selected entry says that the generated dispatch tactic can rely on definitional reduction of the decoded body.  I will remove the premature rewrite and invoke `wp_fixed_array_length_le_dispatch_from hArray at 7, 8` directly on `func0Def.body`; its `change` should reduce `func0Def.body` and recognize the exact prefix.  Progress remains the valid-size and invalid-size branch pair, and failure would justify an explicit `change` to the named dispatch and suffix programs.

## 2026-08-11: Entry-frame premises

The import check accepted the second edit, and the Lean build confirmed that the direct dispatch recipe applies.  The residual goals comprise the valid branch under `input.size ≤ 8`, the invalid branch under its negation, and five entry-frame premises: parameter projection, empty values, `0 < 7`, local 7 within the 20 generated locals, and `8 < UInt64.size`.  This is the expected stronger boundary, so I will keep the recipe result.

Before reducing the frame premises, I searched `PROOF_RECIPES.json` and the `proof-construction`, `loops`, and `compiler-motifs` indexes for `toLocals`, `numParams`, `frame.*params`, `frame.*values`, `locals.*length`, and `local-frame`.  The recipe names generated accessors only for the later array-fold continuing frame, and those accessors do not project the initial `func0Def.toLocals` frame.  The search also identified the `local-frame-projection` entry, whose `Frame.ext` and `withValues_*` declarations concern equality, operand-stack replacement, and internal getters rather than initial function-frame construction.

I inspected `LTG/entries/local-frame-projection/entry.json` and its `README.md`, then rejected it for these five premises.  The already selected length-dispatch README names definitional normalization with `func0Def`, `Function.toLocals`, `Function.numParams`, and `ValueType.zero` for this exact situation, so direct reduction is the catalog-supported method.  I will discharge the five premises with a focused `all_goals simp [func0Def, Wasm.Function.toLocals, Wasm.Function.numParams, Wasm.ValueType.zero]` attempt and leave the two semantic branch goals open.

## 2026-08-11: Branch allocation boundary

The import check accepted the frame-premise edit.  The Lean build discharged the parameter, value-stack, local-index, and local-count premises, while plain `simp` made no progress on the closed goal `8 < UInt64.size`; the two branch goals now carry `hSize : input.size ≤ 8` and its negation.  I will replace the failed closed-goal simplification with `norm_num [UInt64.size]`.

I inspected the `fixed-array-capacity` and `fixed-array-allocation` entry metadata and READMEs after the branch diagnostic.  The capacity entry applies exactly to the annotated length-one and length-zero prefixes and supplies `capacityFrame_internal_get_capacity`; the allocation entry applies to the decoded shifted allocator at offset 2 with four trailing locals and supplies `FixedArrayAllocatorWindow.region_spec_withTail`, `allocFrame_get_root`, and `FixedArrayPairResult.input_preserved_by_alloc`.  I selected both entries because the valid and invalid branch instruction vectors refold definitionally as `constantProgram 1 1 11` or `constantProgram 0 1 11`, followed by `region 2 1`.

For the later fold boundary, I inspected the metadata and READMEs for `fixed-array-fold-structure`, `array-fold-prefix`, `fixed-array-fold-body`, `fixed-array-traversal-input`, `guarded-back-edge`, `annotated-fold-frame-accessors`, `compact-loop-suffix-boundary`, and `fixed-array-result`.  I selected the setup, prefix, combined fold-body, generated accessor, arbitrary-postcondition singleton suffix, and result-store declarations because they match `leanexe.array.fold.v1` and the current multiplication accumulator.  The traversal and guarded-back-edge entries will be used through `FixedArrayFoldBody.continuingGuardedProgram_spec`; I rejected the separately indexed singleton-wrapper entry because its required `leanexe.array.singleton-wrapper.v1` and direct-call shape do not occur in this artifact.

The next proof edit will apply each exact capacity theorem and then `region_spec_withTail 2 4` with capacities 16 and 8.  I inspected the allowed mirrored sources for `FixedArrayCapacity`, `FixedArrayAllocator`, `FixedArrayAllocatorWindow`, `Allocation`, and `FixedArrayPairResult` to confirm the theorem parameters and named store/frame endpoints.  Progress means that each branch reaches a post-allocation continuation, with the valid branch starting at the length store and fold region and the invalid branch starting at the empty-array length store.

## 2026-08-11: Invalid-branch composition diagnostic

The import check accepted the allocator and result-module imports.  The Lean build confirmed the exact invalid-branch refolding, capacity theorem, shifted allocator theorem, zero-length store theorem, root-transfer theorem, and outer continuation shape.  The remaining invalid-branch errors are projection normalization details: broad `simp` did not use the named `capacityFrame_*` and `branchFrame_*` projections, the allocator root theorem needs the capacity-frame length rather than the allocation-frame length, and the final result needs an explicit change from the frozen `FormalSpec.UInt64ArrayAt` definition to the identical ProofKit predicate.

The capacity getter retrieval succeeded: `capacityFrame_internal_get_capacity` matched the allocator's internal slot, leaving only its lower-bound and validity premises.  I will discharge those premises with `capacityFrame_params`, `capacityFrame_locals_length`, `branchFrame_params`, and `branchFrame_locals_length` rather than unfolding list updates.  The allocator root getter will receive a separately named `hCapacityLocals`, while the output conversion will simplify `FormalSpec.expected` under the invalid-size hypothesis and then change the predicate to `UInt64Array.At`.

The closed capacity premise also remained as `8 ≤ (8 : UInt64).toNat`, so the next edit will use a definitional `change 8 ≤ 8` followed by arithmetic.  This diagnostic exposed no new semantic goal class and requires no additional LTG entry.  The valid branch remains untouched and is the only goal outside these invalid-branch projection corrections.

## 2026-08-11: Invalid branch complete

The import check accepted the projection corrections, and the Lean build closed the invalid branch.  The accepted composition uses `constantProgram_spec`, `capacityFrame_internal_get_capacity`, `region_spec_withTail`, `allocFrame_get_root`, `lengthStore_spec`, `emptyStore_at`, `finishProgram_spec`, and `finishFrame_return_get`, then executes the dispatch suffix and proves the frozen expected array is empty.  The only residual goal is the valid branch under `hSize : input.size ≤ 8`.

I will now define the loop's semantic frame, invariant, and getter-based measure.  The frame will use the compiler-generated `function_0_array_fold_0_continuing_frame`, with local 1 equal to `ArrayFold.foldPrefix input (fun product element => product * element) 1 index`, local 13 equal to `UInt64.ofNat index`, and stable input, size, and result-root locals.  The next extended edit will compose valid capacity 16, allocation, length-one storage, preserved input representation, and `forwardSetupProgram_spec`, then apply the block and loop rules; reaching invariant-initialization and loop-step goals will count as progress.

## 2026-08-11: Loop-rule boundary reached

The import check accepted the semantic loop definitions and valid-branch composition.  The Lean build reached exactly two `wp_loop_cons` obligations: `ProductLoopInv` for `forwardSetupFrame` and the body theorem from an arbitrary invariant state.  One incidental line tried to use the local value `allocFrame` as a rewrite theorem; I will replace that `rw` with `simp only`, which preserves the already established parameter endpoint.

The initialization goal requires the concrete equality between the checked setup frame and `productLoopFrame` at index zero.  I will construct its existential witnesses `(0, 0, 0, inputPtr, 0, 0)` and reduce only `forwardSetupFrame`, `productLoopFrame`, the generated scalar-frame constructor, and the already named allocation/capacity/entry frames.  For the step, I will first destruct and substitute the invariant witnesses; the resulting exit-versus-continuing goal will determine the next exact FoldBody application.

## 2026-08-11: Initialized frame and semantic step

The import check accepted the invariant proof attempt.  The initialization reduction closed every field except `heapTop + 48 = root`, which is the local definition of the allocated root and will close by adding `root` to the focused simplifier.  The step now begins at `continuing_program ++ step_program` over the exact `productLoopFrame` and carries only `index ≤ input.size` plus the five unconstrained scratch values.

I will split the step on `index = input.size`.  The equality case uses `continuingProgram_exit_spec`, generated getters 13 and 15, and the generated `function_0_array_fold_0_singleton_result_spec`; its arbitrary postcondition will execute the outer local-6 suffix and establish the singleton representation with `singletonStore_at`.  The strict case will remain for `continuingGuardedProgram_spec`, so successful exit composition will leave one residual goal class: invariant-preserving multiplication and index increment.

## 2026-08-11: Exit suffix composed

The import check accepted the exit composition.  The Lean build applied the exit guard, generated singleton suffix adapter, result-frame accessors, root transfer, and public continuation; three address-bound proofs remained because arithmetic did not normalize the local `loopSt` and `allocSt` page projections, and two `rw` calls again treated the local abbreviation `placedFrame` as a theorem.  The strict continuing case is now the only semantic step left after those local corrections.

I will name `hLoopPages`, `hFitMemoryNat`, and `hFit32Nat`, then derive the payload and root bounds by rewriting to the allocator's original page count.  I will use `simp only [placedFrame, resultFrame_params]` and its local-length analogue for the frame projections.  After these changes, I will instantiate `continuingGuardedProgram_spec` with the generated loaded-frame equality and scalar evaluator equations.

## 2026-08-11: Continuing-branch parser boundary

The import check accepted the continuing-branch edit, and the Lean build no longer reported any exit-branch goal.  Parsing failed at the local element binding and then produced cascading syntax errors throughout the scalar-state arguments, so the build did not yet test the direct fold-body composition.  The dependent array access also generated an unsolved bound metavariable even though `hIndexLt` was in scope.

I will rename the local binding from `value` to `element` and supply `hIndexLt` explicitly to the array getter.  This edit leaves the selected `FixedArrayFoldBody.continuingGuardedProgram_spec` recipe and its generated evaluator equations unchanged.  Progress means that Lean elaborates the composition and reports only theorem premises or state-equality goals.

## 2026-08-11: Accumulator parser boundary

The import check accepted the explicit array getter, and the Lean build eliminated its bound metavariable.  Lean parsed `prefix` as syntax rather than the intended local identifier, producing another cascade before the fold-body theorem could elaborate.  The exit branch remains closed, and no semantic residual goal arose from this check.

I will rename `prefix` to `accumulator` throughout the continuing branch.  The new name preserves the exact `productPrefix input index` definition and every scalar transition argument.  A successful elaboration should now test the theorem premises and the invariant-preservation proof.

## 2026-08-11: Named fold-body premises

The import check accepted the accumulator rename, and the Lean build elaborated `continuingGuardedProgram_spec`.  Positional tactic bullets shifted after Lean inferred dependent premises, so `hItemValid`, `hInputLoop`, and `hIndexLt` were checked against later goals; the remaining diagnostics comprised the loaded-frame equality, item-local numeric bound, body evaluator, condition callback, and logical-index bound.  This residual class matches the selected fold-body entry rather than exposing a new control-flow boundary.

I searched `PROOF_RECIPES.json` and the `loops`, `arrays`, `proof-construction`, and `compiler-motifs` indexes for `continuingGuardedProgram_spec`, `dynamicResultFrame`, `hItem`, `itemLocal`, and `validIndex`.  I re-inspected the canonical `fixed-array-fold-body` entry and used its instruction to name every structural and dependent premise; I rejected no newly found entry because all four indexes pointed to that same canonical entry.  The recipe's exact accessors `function_0_array_fold_0_continuing_item_valid` and `function_0_array_fold_0_continuing_loaded_frame_eq` discharge the item bound and loaded-frame projection without reducing the frame.

I will replace the positional application with a `refine` that supplies `hValues`, all three getters, the encoded index, guard, item validity, input representation, logical bound, and step-program equality by name.  Five explicit holes will remain for the loaded frame, body evaluator, condition evaluator, impossible exit callback, and invariant-preserving continuation.  Progress means that these holes elaborate in that order and the existing fold-prefix successor argument becomes the only possible semantic residual.

## 2026-08-11: Generated next-frame equality

The import check accepted the named fold-body premises, and the Lean build closed the body evaluator, condition evaluator, impossible exit, continuing evaluator, structural premises, and index bound.  The loaded-frame accessor reduced its dependent side to the generated continuing frame but left the definitional equality with `loadedU`; the invariant callback reached its next-frame equality, where unrestricted `simp` exceeded its maximum step count.  These are the two remaining frame-equality boundaries.

I searched `PROOF_RECIPES.json` and the `proof-construction`, `loops`, and `compiler-motifs` indexes for `nextU`, `toState.toLocals`, `continuing_frame`, `frame equality`, `U64State.toState`, and `loaded_frame_eq`.  The recipe selects `function_0_array_fold_0_continuing_loaded_frame_eq`, and I re-inspected the `annotated-fold-frame-accessors` entry, which supports generated constructor and getter use.  The indexes also returned the previously inspected `local-frame-projection` entry, which I rejected here because `Frame.ext` would split one generated-constructor equality into parameter, local-list, and value-stack goals.

I will close the loaded frame by adding the generated continuing-frame definition and the two local abbreviations to the restricted simplifier.  For the next frame, I will `change` both sides to applications of the same generated constructor and rewrite only `hPrefixSucc` and `hIndexSucc`.  Progress means that the invariant reconstruction and getter-based measure proof become the only remaining obligations.

## 2026-08-11: Loaded-frame accessor application

The import check accepted the focused frame reductions, and the Lean build closed the next-frame equality, invariant reconstruction, and measure decrease.  One loaded-frame equality remains because the restricted simplifier unfolded the generated continuing frame before matching `function_0_array_fold_0_continuing_loaded_frame_eq`.  The diagnostic shows identical generated scalar states on both sides after replacing the loaded item, so no new semantic fact is missing.

The preceding recipe and LTG search already selected the exact loaded-frame accessor for this residual class.  I will pass that theorem as the proof term to `simpa`, using only `productLoopFrame`, `loadedU`, `accumulator`, `element`, and the generated frame definition for normalization.  This removes rewrite-order dependence while retaining the checked dependent local-update theorem.

## 2026-08-11: Acceptance

The final import check succeeded, and the required leanrunner build completed all 3,082 jobs, including `LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactResult`.  The accepted proof uses the shared length-dispatch, capacity, shifted-allocation, array-representation preservation, fold setup, loop, fold-body, prefix, frame-accessor, result-store, and public-continuation declarations selected through the recorded LTG searches.  `artifact_behavior` has no residual goal, and `Behavior.lean` was not edited after acceptance.
