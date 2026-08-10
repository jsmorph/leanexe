# Checked fixed-array fold structure

Use `FixedArrayFold.forwardSetupProgram_spec` when a `leanexe.array.fold.v1` recipe supplies `<region>_setup_eq`.  The exact matcher restricts this theorem to a forward, one-word, one-accumulator fold over the complete input array in the standard one-parameter wrapper.  It executes both represented-length loads, initializes the array pointer, index, accumulator, and release state, selects the effective stop, and reaches `forwardSetupFrame` for an arbitrary continuation.

Prove the setup theorem's writable-local premise from the generated frame length, and prove its `setupLocals` list has no duplicates by reduction.  The named frame retains every unrelated local because it changes only the eight listed destinations.  State the loop invariant on that frame and apply the block and loop rules without reducing the setup instructions or the nested local-update chain.

Use `FixedArrayFold.resultProgram_spec` when the same recipe supplies `<region>_result_eq`.  It copies one selected accumulator local to one result local and reaches `resultFrame`, preserving parameters, all other locals, and the empty value stack.  Apply it after `ArrayFold.foldPrefix_size` has rewritten the completed accumulator to the specification's `Array.foldl` value.

The setup theorem does not constrain the fold step, accumulator meaning, or result theorem.  `array-fold-prefix` supplies the mathematical prefix relation, `fixed-array-traversal-input` executes a continuing guard and indexed load, and `fixed-array-result` handles later output stores.  Reverse traversal, multiple source words, multiple accumulators, a non-input array expression, or a nonstandard setup remains outside this exact program and requires another checked shape.
