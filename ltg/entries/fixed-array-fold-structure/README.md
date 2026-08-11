# Checked fixed-array fold structure

Use `FixedArrayFold.forwardSetupProgram_spec` when a `leanexe.array.fold.v1` recipe supplies `<region>_setup_eq`.  The exact matcher restricts this theorem to a forward, one-word, one-accumulator fold over the complete input array in the standard one-parameter wrapper.  It executes both represented-length loads, initializes the array pointer, index, accumulator, and release state, selects the effective stop, and reaches `forwardSetupFrame` for an arbitrary continuation.

Prove the setup theorem's writable-local premise from the generated frame length, and prove its `setupLocals` list has no duplicates by reduction.  The named frame retains every unrelated local because it changes only the eight listed destinations.  State the loop invariant on that frame and apply the block and loop rules without reducing the setup instructions or the nested local-update chain.

The structured `wp_block_loop` tactic record identifies a block-wrapped `Wasm.wp` loop goal and requires an explicit invariant and natural-number measure.  The command applies the block and loop rules together, while `Wasm.wp_loop_cons` remains its indexed fallback for proofs that need direct control over either rule.  The record is restricted to the array-fold annotation kind in this entry.

Use `FixedArrayFold.resultProgram_spec` when the same recipe supplies `<region>_result_eq`.  It copies one selected accumulator local to one result local and reaches `resultFrame`, preserving parameters, all other locals, and the empty value stack.  Apply it after `ArrayFold.foldPrefix_size` has rewritten the completed accumulator to the specification's `Array.foldl` value.

Use `resultFrame_get_result` to read the written result local and `resultFrame_get_of_ne` to preserve any distinct valid nonparameter local.  The generated continuing-frame parameter, local-length, and getter theorems discharge their frame premises without reducing the scalar state.  The `annotated-fold-frame-accessors` entry gives the restricted simplification form and the checked Demo 9 substitution evidence.

Use `resultFrame_params`, `resultFrame_locals_length`, and `resultFrame_values` when a generated completion adapter leaves frame-shape premises after result placement.  Rewrite those projections before applying generated completion-frame declarations.  This sequence preserves the named result frame and avoids unrestricted simplification of its local update.

Use `FixedArrayFold.singletonResultProgram_spec` when the recipe also supplies `<region>_singleton_result_eq`.  The theorem composes accumulator placement, the standard singleton payload store, and final root transfer, then reaches `singletonResultPost` with the returned root and represented singleton value.  Its local indices and frame facts remain parameters, so the checked program applies across fold operations and wrapper layouts that emit the same suffix.

Prefer `<region>_singleton_result_spec` when the recipe supplies the generated adapter.  It discharges the generic theorem's frame premises through exact continuing-frame accessors and invokes `singletonResultProgram_spec_to` with the caller's postcondition.  The caller retains the mathematical fold equality, payload bound, represented result, and public-return argument.

If `Wasm.wp_loop_cons` retains the result program and complete public postcondition until elaboration reaches the memory limit, consult `compact-loop-suffix-boundary`.  A nested `Wasm.wp.conseq` may suffice when its implication remains small.  Apply the complete singleton theorem or place another suffix theorem in a preceding declaration when the implication still elaborates inside the large public theorem.

The setup theorem does not constrain the fold step, accumulator meaning, or result theorem.  `array-fold-prefix` supplies the mathematical prefix relation, `fixed-array-traversal-input` executes a continuing guard and indexed load, and `fixed-array-result` handles later output stores.  Reverse traversal, multiple source words, multiple accumulators, a non-input array expression, or a nonstandard setup remains outside this exact program and requires another checked shape.
