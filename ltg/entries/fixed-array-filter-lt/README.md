# Bounded stable UInt64 filter

Use this entry when `PROOF_RECIPES.json` reports `leanexe.array.filter-lt.v1` over the complete exported function.  The checked generated equality connects the decoded function to `FixedArrayFilterLt.wrapperProgram maximumSize threshold`.  `wrapperProgram_spec` then covers length dispatch, input-sized allocation, the filtered-prefix loop invariant, conditional payload stores, dynamic result length, the invalid-size allocation, and public return.

Apply the complete theorem before any loop, allocator, or branch-level recipe.  The schema-6 formal interface supplies `heapReserveBytes`, whose bound accounts for reserved capacity even when filtering produces a shorter array.  If the deterministic starter already applies this theorem, run the prescribed check before editing and retain the starter when Lean accepts it.

The current theorem specializes the predicate to unsigned comparison with a constant threshold.  That scope makes the entry a compiler motif rather than a general array-filter theorem.  A different predicate should receive a separate semantic adapter or a more general checked theorem when another artifact establishes the recurring shape.
