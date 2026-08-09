# Proof Journal

## Initial check

I ran the required build against the untouched candidate.  The build reached `Behavior.lean` and failed at line 16 with the starter context fully decomposed by `RuntimeReady`.  The remaining goal is `TerminatesWith env module 0 initial [Value.i64 inputPtr]` with the expected result-array postcondition.

The context already contains the six globals, the input representation and length read, the input-address normalization, all output and heap bounds, and the relevant global lookups.  The proof therefore needs the generated execution theorem and its loop/allocation support rather than more decomposition of `RuntimeReady`.  I began LTG retrieval with `LTG/categories.json`, whose relevant categories are compiler motifs, loops, arrays, allocation, memory, and proof construction.

## Catalog searches and direct recipe

I searched the compiler-motif, array, and proof-construction indexes for `leanexe.array.length-dispatch.v1`, `FixedArrayLengthDispatch`, `wp_fixed_array_length_le_dispatch`, and `leProgram_spec`.  That query returned no LTG entry, although `PROOF_RECIPES.json` supplies the exact checked theorem and tactic directly.  The recipe applies to function 0, region `function-0.length-dispatch-0`, input local 7, and maximum size 8.

I searched the loop, compiler-motif, and proof-construction indexes for `loop-carried`, `accumulator`, `foldl`, `scalar`, `loop`, `invariant`, and `post-test`.  The relevant generic entry is `scalar-post-test-loop`; `counter-transition` concerns a decrement/increment identity, `euclidean-gcd-loop` concerns remainder arithmetic, and the two counter-transfer examples require different annotations and state transitions.  I rejected the filter and map entries because their whole-function annotations and expected functions do not match this fold-sum artifact.

I searched the array, allocation, and memory indexes for `singleton`, `allocation`, `fixed array`, `result`, `UInt64Array`, and `array`.  The relevant support entries are `fixed-array-allocation` for the bump allocator and `residual-specification-normalization` for the final singleton equation.  I deferred `fixed-array-singleton-wrapper` because its indexed shape includes a direct scalar call, while this function has no calls and performs the traversal in function 0.

I inspected `PROOF_RECIPES.json` before reducing any recipe instructions and selected its direct tactic `wp_fixed_array_length_le_dispatch 7, 8`.  I added that exact invocation at the starter goal without unfolding the annotated region.  The next prescribed check will determine whether the recipe completes the proof or exposes the two branch obligations described by its expected postcondition.

The import check accepted the candidate, but the Lean build rejected the direct invocation at line 33.  The tactic tried to change a `wp` goal beginning with `FixedArrayLengthDispatch.leProgram 7 8`, while the current target remained the public `TerminatesWith env module 0 initial [Value.i64 inputPtr]` statement.  This is a proof-boundary mismatch: the selected region theorem still applies after converting the exported function execution to its instruction-level weakest precondition.

The direct recipe did not expose its branch postconditions because function-entry reduction has not occurred.  I will search the proof-construction index for `TerminatesWith`, entry conversion, `wp_entry`, and function-start declarations, then inspect only the entries that identify the matching boundary theorem.  The missing catalog guidance is an explicit composition from the public `TerminatesWith` goal to the checked length-dispatch tactic.

The proof-construction, compiler-motif, and loop indexes contain no entry matching the query `TerminatesWith|wp_entry|entry-to|function entry|function-start|wp_start|terminates_with`.  `strategy.loops` names `Project.ProofKit.Control.wp_entry_to_loop`, so I confirmed the adjacent `wp_entry` macro and CodeLib's `Wasm.TerminatesWith.of_wp_entry_for` signature in their dependency sources.  The store-specific theorem fits this proof because every `RuntimeReady` fact concerns the quantified `initial` store.

I inspected the `scalar-post-test-loop` entry and rejected it for the present Program.  Its theorem requires an exact `leanexe.loop.scalar-post-test.v1` descriptor-region equality, while `PROGRAM_ANNOTATIONS.json` records only the length-dispatch annotation.  The missing support is a checked traversal-loop descriptor for an array fold with a loop-carried sum, not scalar-loop mathematics.

I inspected the `fixed-array-allocation` entry and retained it for the valid branch.  The decoded valid branch starts with LeanExe's fixed-array allocation sequence, and `RuntimeReady` supplies the entry's empty-free-list, existing-memory-fit, page-bound, and allocator-global premises.  Its region theorem may become necessary after the length dispatch exposes the valid branch.

I inspected the `residual-specification-normalization` entry and rejected its specific normalization recipe.  It assumes a singleton input and reduces `Array.size_eq_one_iff`, whereas the requested valid branch accepts every input size through eight and returns the input fold.  Unfolding `FormalSpec.expected` under the valid or invalid size fact remains useful, but this entry's complete singleton-wrapper composition does not match.

I confirmed that `func0Def` is function index 0 with one `i64` parameter, twenty `i64` locals, the generated `func0` body, and one `i64` result.  I added `Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl` immediately before the unchanged direct recipe.  This composition preserves all store-specific premises and presents the exact body-level `wp` goal expected by the recipe.

The import check passed, and the build confirmed that the entry conversion gives the recipe its expected `wp` shape.  The recipe decomposed the program into valid and invalid branch obligations, but `apply leProgram_spec` left its `inputPtr` and `input` arguments as metavariables, producing separate type goals and preventing `hArray` from closing the representation premise.  The elementary frame, positivity, local-bound, and maximum-size premises also remain because the direct macro only applies the theorem.

The residual boundary is better: the large target now begins at each post-dispatch branch, and the expected continuation is explicit.  I will replace the macro's internal `apply` with the same `change` and an explicit `leProgram_spec (inputPtr := inputPtr) (input := input)` application, then discharge its structural premises before addressing either branch.  Before that edit, I will search LTG for array-fold, wrapping-sum, indexed traversal, and accumulator declarations matching the valid branch.

I searched the loop, array, compiler-motif, and proof-construction indexes for `fold`, `foldl`, `sum`, `wrapping`, `accumulator`, `traversal`, `indexed`, and `prefix`.  No entry supplies an array-fold or wrapping-sum loop theorem; the only accumulator match is the scalar post-test descriptor already rejected for lack of its required annotation.  The map, filter, counter, GCD, and singleton-wrapper entries describe different complete instruction shapes and semantic results.

I inspected `PROOF_LIBRARY.md` for `fold` and `sum` declarations and found no array-fold theorem.  Its applicable components are the length-dispatch theorem already selected, the fixed-array allocator support named by LTG, generic control rules, array-read facts, and fixed-array result construction.  The catalog lacks a checked annotation and theorem for this common bounded fold-sum loop, so the valid branch will require an explicit invariant over an input prefix.

I replaced the macro with its exact `change` target and direct theorem application, supplying `inputPtr` and `input` explicitly.  The first six premises use the generated entry frame, decidable numeric bounds, and `hArray`.  I left the branch premises open so the next diagnostic will display each branch with all metavariables resolved.

The import check passed, and the explicit recipe application resolved `inputPtr` and `input` as intended.  Lean accepted the parameter-frame, value-stack, positive-local, maximum-size, and array-representation premises, then exposed only the valid and invalid program branches.  The local-index bound failed because `decide` requires a closed expected type before reducing `func0Def.toLocals`, and the reducible expression still mentions the free `inputPtr`.

I will normalize the generated function and local frame for that one numeric premise with `norm_num [func0Def, Wasm.Function.toLocals]`.  This change addresses the presentation of the local-count fact while keeping the recipe boundary intact.  The branch diagnostics confirm that no unresolved theorem parameters remain.

The import check passed after local-frame normalization, and the build now reports only the two branch premises.  I matched both branch allocators to `FixedArrayAllocatorWindow.region 2 1`: capacity occupies combined local 11, the allocator scratch window starts at offset 2, the returned root occupies combined local 7, and four trailing locals make the twenty-local frame.  The valid prefix computes capacity 16, while the invalid prefix computes the minimum capacity 8.

I used the `fixed-array-allocation` entry by selecting `FixedArrayAllocatorWindow.region_spec_withTail 2 4`.  I also retained `FixedArrayPairResult.input_preserved_by_alloc`, which the checked result support exposes for transporting the input representation across the six allocator header writes.  `FixedArrayResult.singletonStore_at` will reconstruct the valid singleton output after the fold, while the empty output can be constructed directly from the invalid branch's length store.

I added local names for the two capacity prefixes, allocator compositions, fold body, valid and invalid suffixes, loop frame, invariant, and measure.  The invariant carries the exact post-length-store memory and relates the loop-carried sum local to `sumPrefix input index`, defined as the fold over `input.extract 0 index`.  `sumPrefix_succ` uses `Array.extract_succ_right`, and `sumPrefix_all` identifies the completed prefix fold with the formal `Array.foldl` result.

The import check passed, but Lean found two errors in the new helpers before reaching the unchanged branch goals.  `Array.extract_succ_right` rewrote the prefix array as a push, after which the fold still needed the explicit `Array.foldl_push` theorem; the broad simplifier did not select that theorem.  The measure's pattern also required `Value.i64` because dotted-constructor notation lacked an expected `Value` type inside the option pattern.

I added the named fold-over-push rewrite and qualified the value constructor in the measure.  Both changes address helper elaboration and leave the artifact program decomposition unchanged.  The next check will validate the prefix algebra before I add branch execution.

The import check passed, and Lean accepted every helper, including both prefix-fold lemmas and the loop measure.  The remaining goals were again the valid and invalid branch programs, which confirms that `validProgram` and `invalidProgram` have not yet affected the public proof.  I proceeded to refold both literal branch bodies through those exact definitions.

Both branches now execute their concrete capacity prefixes and apply `FixedArrayAllocatorWindow.region_spec_withTail 2 4`.  The valid branch supplies capacity 16 and reaches the allocator continuation with its fold suffix still folded.  The invalid branch supplies capacity 8, executes the zero-length store and return-local moves, and reconstructs `UInt64Array.At` for the empty result using the allocator's root arithmetic and the write-at-same-address theorem.

The import check passed, and Lean accepted the complete invalid branch.  Its only remaining diagnostic is the valid allocator continuation, stated as `wp module validSuffix` over the named allocation store and offset-two allocation frame.  This confirms the allocator region matches exactly in both branches and removes two of the artifact's three loops from the remaining proof.

For the valid continuation, I derived the bump root address and transported `hArray` first across the allocator header stores and then across the output-length store.  The resulting `hInputResult` describes the original input in the exact store from which the traversal loop reads.  I began symbolic execution of `validSuffix` through its output-length store so the next diagnostic identifies the first setup or loop boundary that still needs a named fact.

The import check passed, and execution reached the intended memory-read boundary after the length store.  A trailing `wp_run` failed with “`simp` made no progress,” which means the current instruction requires a load bound or read equation rather than more straight-line reduction.  I removed that tactic call so Lean will print the exact residual goal and address form on the next build.

The next build exposed two identical input-length load conditions, both over allocator memory whose pages equal the initial pages.  The load values occur in the post-length-store memory, exactly the store represented by `hInputResult`; no application fact is missing.  I added one allocator-page-normalized bound, used `hInputResult.pointerAddress_eq` and `lengthRead` for both reads, selected the equal-length side of the emitted minimum, and reached the block-wrapped traversal loop.

I applied `wp_loop_cons` with `foldInv` and `foldMeasure`.  The initialization uses index zero, sum zero, an untouched element local, the input pointer in the scratch local, and flag zero, matching the generated setup frame.  The next diagnostic will test that exact initialization and expose the loop-body preservation obligation.

Lean accepted both load-bound rewrites and the pointer-address normalization.  The remaining rewrite failed because symbolic execution exposes the length-store memory as a direct record update, while `hInputResult.lengthRead` retains the named `FixedArrayResult.writeLength` definition.  I added `hInputResultLength`, an exact direct-store form obtained by simplifying that named definition, and will use it for both loaded length words.

The direct length-read equation closed the setup and Lean accepted the loop invariant initialization.  The sole residual goal is the loop step, with the generated block and post-loop payload store preserved in the continuation.  This confirms that the frame definition matches all twenty locals at loop entry.

I implemented the loop step by splitting on `index = input.size`.  The repeat branch uses `hInputResult.generatedElement`, updates the sum through `sumPrefix_succ`, preserves the exact read-only store, and decreases `input.size - index`; the exit branch writes the accumulated sum to the singleton payload and applies `FixedArrayResult.singletonStore_at`.  The proof uses one indexed transition for every iteration and contains no fixed set of eight element cases.

The build found three presentation mismatches inside the loop step.  The payload address theorem retains an intermediate `2^64` modulus, the exit branch had already reached its store condition before a redundant `wp_run`, and the repeat branch's load remains expressed through the named `writeLength` store rather than the unfolded record.  None changes the invariant or semantic transition.

I normalized the payload address with the allocator's root bound, removed the redundant exit-branch execution call, and retained the named store in the indexed load equation.  I also normalized the payload bound through `writeLength_pages` at its use site.  These forms now match the exact residual terms printed by Lean.

The repeat branch now checks through its indexed read, prefix update, invariant reconstruction, and strict measure decrease.  In the exit branch, Lean attempted to apply the payload bound to the body-load alternative because the surrounding `br_if` continuation had not reduced before the rewrite.  The later constructor errors follow from that first control-flow mismatch.

I now simplify `FixedArrayEqNode.branchPost` immediately after rewriting the true loop guard.  This follows the checked map-loop composition and reduces the `br_if` match to the post-loop payload continuation before any memory-bound rewrite.  The payload condition then has the root-plus-eight address covered by `hPayloadBound`.

Simplifying the continuation alone did not execute the true `br_if`; the payload rewrite still encountered the body-load alternative first.  The checked loop composition performs `wp_run` after that continuation simplification, so I restored the execution call at that later point.  Its earlier placement failed because the continuation had not yet been normalized.

The later `wp_run` succeeds, but the following rewrite still selects a body-load condition, and a subsequent execution call reports no progress.  I removed the rest of the exit branch temporarily, leaving the normalized post-guard goal as the first diagnostic.  That goal will show whether the loop rule presents the exit as a nested match, conjunction, or direct payload continuation.

The diagnostic shows `match [Value.i32 1]` with the zero case containing the next-iteration input load and the nonzero case containing the post-loop payload store.  Generic rewriting descends into the zero case before reducing this match, which explains the repeated address mismatch.  I added an exact `change` to the nonzero case's payload-store conditional, then restored the payload write, returned-pointer proof, and singleton representation.

The next import check passed, and the Lean build accepted the explicit payload-store page condition and the address rewrite.  The following `wp_run` made no progress because the goal had already reduced past the store instruction to its postcondition.  I removed that tactic so the result-pointer witness can discharge the remaining return-state match directly, and I removed an unused `foldFrame` simplifier argument reported by Lean.

The required import check returned successfully after that edit.  The bounded build then compiled `Behavior` and `ArtifactResult` without diagnostics, proving that the loop invariant and both length-dispatch branches establish the frozen artifact specification.  I left the candidate unchanged after this successful check and scheduled the required final import-and-build pair.
