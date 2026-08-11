# Proof Journal

## 2026-08-11: Initial candidate check

The required import check succeeded on the unchanged candidate.  The first Lean build failed at `Behavior.lean:23:116`, after the deterministic `RuntimeReady` decomposition and common array facts.  The residual goal is `TerminatesWith env module 0 initial [Value.i64 inputPtr]` with the expected existential result pointer and `FormalSpec.UInt64ArrayAt final outputPtr (FormalSpec.expected input)` postcondition.  The context contains `hArray`, `hLengthRead`, `hLengthBound`, `hInputAddress`, `hHeapTop`, `hFreeList`, and `hAllocs`, together with all input, output, heap-reserve, and page bounds.  No execution proof has yet been attempted.

## 2026-08-11: Initial recipe and LTG retrieval

Retrieval began with `LTG/categories.json`.  I searched the `arrays`, `loops`, `compiler-motifs`, `proof-construction`, and `allocation` indexes with `rg -n 'length-dispatch|array\.fold|TerminatesWith|wp_fixed_array_length_le_dispatch_from|singletonResult|foldPrefix|FixedArrayCapacity' .../tools.jsonl`.  The query returned the exact `fixed-array-length-dispatch` entry for the current annotation and starter goal, along with fold, traversal, capacity, result, frame-accessor, and loop-boundary entries that may apply after dispatch.

I inspected `LTG/entries/fixed-array-length-dispatch/entry.json` and its `README.md`.  Its structured tactic has the required `leanexe.array.length-dispatch.v1` annotation, requires the represented input array already present as `hArray`, and expects the body-level `Wasm.wp` goal obtained through `Wasm.TerminatesWith.of_wp_entry_for`.  I selected this entry.  The task-specific recipes contain no complete composition.  Their first direct recipe is the same entry and prescribes `wp_fixed_array_length_le_dispatch_from hArray at 7, 8`, while the fold recipe begins only inside the valid branch.

The next candidate edit will apply `Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl`, rewrite the decoded body with the checked function equality if needed, and invoke the exact dispatch tactic before reconstructing `leProgram_spec`.  Progress means replacing the public termination goal with separate valid-branch and invalid-branch weakest-precondition obligations.  A mismatch in entry conversion, frame shape, or decoded-body decomposition will count as rejection of the tactic's current shape and trigger another LTG checkpoint.

## 2026-08-11: Direct length-dispatch result

The import check passed after the first proof edit.  The Lean build failed with six residual goals, which is the expected improvement: four initial-frame premises (`hParams`, `hValues`, positive input-local index, local-list bound, and the UInt64 maximum-size bound as grouped by the diagnostic) and the valid and invalid branch `wp` obligations.  `Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl` produced the body-level goal, and the structured command `wp_fixed_array_length_le_dispatch_from hArray at 7, 8` matched without a manual function rewrite.  I therefore used the `fixed-array-length-dispatch` entry and its tactic.  Its fallback declaration `FixedArrayLengthDispatch.leProgram_spec` is unnecessary because the command produced a smaller boundary.

The valid branch begins with the checked constant-capacity motif, then allocator code, the annotated fold, a singleton payload store, and the root transfer.  The invalid branch has the same allocator shape with capacity for an empty array and then stores an empty-array length.  Before reducing the initial frame premises or entering either allocator, I will search the recipes and LTG indexes for exact frame projections and allocation-region theorems.

## 2026-08-11: Frame and allocator retrieval checkpoint

I searched the `arrays`, `allocation`, `memory`, `proof-construction`, and `compiler-motifs` indexes with `rg -n 'branchFrame_params|branchFrame_locals_length|branchFrame_values|Function\.toLocals|numParams|fixed-array-allocation|region_spec_withTail|constantProgram_spec|singleton-wrapper|emptyStore_at' .../tools.jsonl`.  No LTG entry or recipe provides exact accessors for the entry frame created by `func0Def.toLocals`; the length-dispatch documentation permits reduction with `func0Def`, `Function.toLocals`, `Function.numParams`, and `ValueType.zero` for these structural premises.  I will therefore close the five entry-frame and numeric premises by reduction and arithmetic.

I inspected the `fixed-array-capacity`, `fixed-array-allocation`, and `fixed-array-result` entries.  I selected `FixedArrayCapacity.constantProgram_spec` for both branch prefixes, `FixedArrayAllocatorWindow.region_spec_withTail` for the allocator at offset 2 with four trailing locals, `FixedArrayPairResult.input_preserved_by_alloc` for the valid branch's input representation, and `FixedArrayResult.emptyStore_at` for the invalid result.  I rejected `fixed-array-singleton-wrapper` from the search results because its annotation kinds require a singleton wrapper and direct call, while this artifact has a bounded length dispatch and an in-function fold.  The result-entry tactics do not yet match: the current goals are branch-level `wp` obligations rather than `UInt64Array.At` goals.

The next small edit closes only the dispatch theorem's structural premises.  The expected residual goals are exactly the valid and invalid branch weakest preconditions.  The following branch construction will retain the capacity and allocator frames and use their named parameter, local-length, value-stack, capacity, and root accessors.

## 2026-08-11: Structural dispatch premises discharged

The import check passed.  The Lean build now reports only `hValid` and `hInvalid`; reduction with the length-dispatch entry's named definitions discharged all five entry-frame and numeric premises.  No lower-level execution was exposed.  This confirms that the branch frame has one parameter, twenty locals, and an empty operand stack.

I will prove `hInvalid` first because it contains no input traversal.  The branch will refold to `constantProgram 0 1 11 ++ region 2 1 ++ lengthStoreProgram 7 0 ++ finishProgram 7 5 6`.  The selected capacity theorem should produce capacity 8, and `region_spec_withTail` should accept offset 2 and tail 4.  Its residual state should be the named allocation store and frame.  `emptyStore_at` should then establish the empty array, and the result-frame getter plus the enclosing branch continuation should close the public return.  Progress means eliminating `hInvalid` while retaining only `hValid`.

## 2026-08-11: Invalid-branch composition diagnostics

The import check passed.  The exact branch refolding succeeded, and Lean accepted `constantProgram_spec`, `capacityFrame_internal_get_capacity`, and `region_spec_withTail` at offset 2 and tail 4.  It also accepted the allocation fit, page, memory-width, and global premises.  The remaining invalid-branch diagnostics are bounded normalization and inference issues: `norm_num` did not close two concrete `UInt64.toNat` facts; `allocFrame_get_root` could not infer its `tail` parameter from a local-length equation; the length-store bound retained a redundant `mod 4294967296`; the public result equation still exposed `func0Def.numParams`; and the shared `UInt64Array.At` output must be changed to the definitionally equal frozen `FormalSpec.UInt64ArrayAt` predicate.

This check used the selected allocation and result entries.  The capacity and allocator declarations reduced the branch to named stores and frames, so I retain them.  The result-entry `emptyStore_at` also succeeded.  I will repair the concrete normalization with computation, pass `tail := 4` to both root-getter applications, normalize the address with `BumpFacts.wordAddress_toNat` and `Nat.mod_eq_of_lt`, transport the output predicate by `change`, and use `Frame.withValues_get`'s defining equality to apply `finishFrame_return_get` after the branch continuation clears the operand stack.  Progress remains the elimination of `hInvalid`.

## 2026-08-11: Invalid branch reduced to one bound

The import check passed.  All invalid-branch goals now close except the length-store memory bound.  `BumpFacts.wordAddress_toNat` already removed the modulo expression, so the subsequent explicit `Nat.mod_eq_of_lt` rewrite has no target and prevents the final use of `hFit`.  The explicit tail arguments, `finishFrame_return_get` through `Frame.withValues_get`, public result-list equation, and frozen output-predicate conversion all succeeded.  I will remove the redundant modulo rewrite and close `heapTop.toNat + 48 + 8 ≤ pages * 65536` directly from `hFit` after rewriting the normalized capacity to 8.

## 2026-08-11: Invalid branch accepted; valid-fold retrieval

The import check passed, and the Lean diagnostic now contains only `hValid`.  The invalid branch is complete through the selected capacity, allocator, empty-result, finish-frame, and public-continuation declarations.

For the valid branch, I inspected `array-fold-prefix`, `fixed-array-fold-structure`, `fixed-array-fold-body`, and `fixed-array-traversal-input`.  I selected `ArrayFold.foldPrefix`, `foldPrefix_succ`, and `foldPrefix_size` for the mathematical accumulator; `FixedArrayFold.forwardSetupProgram_spec` for setup; the structured `wp_block_loop` command for the annotated block-wrapped loop; `FixedArrayTraversalInput.continuingProgram_exit_spec` for the size boundary; and `FixedArrayFoldBody.continuingGuardedProgram_spec` with the generated scalar evaluator equalities for a continuing iteration.  The `wp_block_loop` record matches the prospective goal shape and annotation kind and requires exactly the invariant and decreasing natural-number measure that the proof will supply, so I will attempt the command before its `Wasm.wp_loop_cons` fallback.

I also searched the memory and array indexes with `rg -n 'frameBefore|writeLength|input_preserved_by_alloc|input preservation|array-memory-framing' .../tools.jsonl` and inspected the `array-memory-framing` entry.  I selected `FixedArrayPairResult.input_preserved_by_alloc` before the result-length store and `UInt64Array.At.write64After` after it.  The entry's `word_reads` tactic does not match because the residual goal is an array-representation preservation fact, so I will use the indexed representation declarations instead.

The next construction adds a named `sumPrefix`, an exact generated `sumFoldFrame`, and a loop invariant carrying the logical index, prefix sum, represented input, fixed loop store, and generated frame.  The valid branch should refold to capacity 16, allocator offset 2/tail 4, the length store, annotated setup, block-wrapped loop, and the complete singleton result suffix.  The next check should reach the invariant initialization and loop-step obligations rather than allocator or instruction-level goals.

## 2026-08-11: Valid prefix and structured loop command

The import check passed.  The valid branch refolded exactly, and Lean accepted capacity 16, the shifted allocator, allocator input preservation, `UInt64Array.At.write64After`, the singleton length store, and `FixedArrayFold.forwardSetupProgram_spec`.  The structured `wp_block_loop` command matched the residual block and produced its documented obligations: `hInit` for the named invariant and `hStep` for invariant-preserving loop-body execution with measure decrease.  A separate `hParams` equation remains because `forwardSetupProgram_spec` inferred a fresh input-pointer metavariable before reaching `hInputLoop`; I will fix its `inputPtr` and `input` arguments explicitly.

The command's effect confirms that the `fixed-array-fold-structure` entry applies, so I used it and do not need its `Wasm.wp_loop_cons` fallback.  The initialization proof will identify the setup frame with `sumFoldFrame` at index zero through the capacity, allocator, dispatch, and generated-frame shape declarations.  The step proof will split on `index = input.size`, use `continuingProgram_exit_spec` on the exit edge, and use `continuingGuardedProgram_spec` on the strict edge.  The strict-edge callbacks will apply `foldPrefix_succ` and prove the `sumMeasure` decrease.

## 2026-08-11: Loop initialization and exit edge

The import check passed.  Explicit setup arguments removed the pointer metavariable, and the generated-frame equality closed the invariant initialization.  The size-equality edge matched `FixedArrayTraversalInput.continuingProgram_exit_spec`, and the checked generated singleton-result adapter reached the final public result.  Three exit-edge details remain: make the payload and singleton fit bounds explicit rather than leaving them to `omega` after address rewrites, and unfold `FixedArrayResult.singletonStore` when transporting the represented output to the adapter's `writePayload (writeLength ...)` store.  The only other residual goal is the strict loop edge with `index < input.size`.

The `fixed-array-traversal-input` exit declaration and generated singleton adapter therefore apply and remain selected.  After closing the explicit fit and store-normalization details, I will apply `FixedArrayFoldBody.continuingGuardedProgram_spec` to the strict edge with the annotation-generated loaded-frame equality, body evaluator, condition evaluator, and step evaluator.  Its false-condition callback should leave only the next `SumInvariant` and decreasing `sumMeasure` facts.

## 2026-08-11: Concrete UInt64 fit normalization

The import check passed.  Unfolding `singletonStore` resolved the output-store equality.  The remaining exit-edge failures are the three explicit fit facts because rewriting `hCapacity` leaves `UInt64.toNat 16` in their hypotheses; `omega` does not reduce that closed UInt64 conversion.  I will run `norm_num` on those hypotheses after the rewrite.  The strict-edge goal remains unchanged and still matches the selected `fixed-array-fold-body` theorem.

## 2026-08-11: Capacity-to-Nat residual

The import check passed, but `norm_num` did not normalize the `UInt64.toNat 16` occurrence retained in the allocator facts.  I will state the exact checked equality `(normalizedCapacity 1 1).toNat = 16` and use `convert` with that equality for the payload, 32-bit, and memory fit premises.  This isolates the machine-word conversion from the natural-number inequalities.

## 2026-08-11: Truncated check and strict-edge construction

The import check passed after adding the exact capacity-to-natural equality.  The build output exceeded the execution transcript limit during context compaction, and the closed execution cell no longer exposes its diagnostic or exit status.  The candidate still ends immediately after `hIndexLt`, so the build could not have produced the target artifact.  I will not repeat the unchanged check.

I re-read the exact `FixedArrayFoldBody.continuingGuardedProgram_spec` declaration, its selected LTG entry, and the recipe's generated supporting declarations.  Its `goalShape` is the current strict traversal edge, its premises match the represented loop input and generated locals 11, 13, 15, and 2, and its annotation kind is `leanexe.array.fold.v1`.  The next edit will attempt that command with the generated loaded-frame equality and the body, condition, and continuing evaluator equations before reconstructing any scalar evaluator.  Progress means reducing the edge to the false-condition callback, where `ArrayFold.foldPrefix_succ` reconstructs `SumInvariant` at `index + 1` and the natural measure decreases.

## 2026-08-11: Acceptance

The final import check succeeded, and the required `leanrun` build produced `LeanExeGen.GeneratedR23fa7efc3fb0298b.ArtifactResult` with only pre-existing unused-variable warnings from `AnnotationMatches.lean`.  `FixedArrayFoldBody.continuingGuardedProgram_spec` accepted the current residual goal and all named premises.  The generated loaded-frame equality, body evaluator, condition evaluator, and continuing evaluator reduced the strict edge to its callback.  `ArrayFold.foldPrefix_succ` established the next wrapping accumulator, the generated index getter exposed the incremented logical index, and arithmetic closed the decreasing measure.

The accepted proof uses the shared length-dispatch, capacity, allocator-window, array-preservation, fold-setup, block-loop, traversal-exit, fold-body, singleton-result, and public-return declarations recorded above.  The theorem now covers both array-length branches and has no residual goal.  The candidate contains no `sorry`, axiom, Source import, or source-code dependency.
