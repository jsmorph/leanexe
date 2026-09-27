# Fixed-array result stores

Use `FixedArrayResult.lengthStore_spec` or `payloadStore_spec` when the residual program begins with the standard generated word store and then continues with application-specific instructions.  Both theorems accept arbitrary combined-local indices, remaining programs, and postconditions, while naming the changed store as `writeLength` or `writePayload`.  Supply exact frame getters before applying either theorem so the proof does not expand the complete generated local list.

Use `singletonStore_at` after one length word and one payload word have been written through `FixedArrayResult.singletonStore`.  Its two premises state that the sixteen-byte representation fits in 32-bit address space and current memory.  `pairStore_at` provides the corresponding twenty-four-byte theorem for two payload words.

Use `emptyStore_at` after writing a zero length for an invalid or oversized-input branch.  It constructs the complete `UInt64Array.At` fact for `#[]` from the eight-byte address-space and current-memory bounds.  This avoids unfolding the representation and rebuilding its vacuous indexed-element case in each wrapper proof.

For a completed fold, first rewrite the accumulator with `ArrayFold.foldPrefix_size`, establish its concrete result-local getter, and apply `payloadStore_spec` to the output store.  Refold the resulting memory as `singletonStore` before applying `singletonStore_at`, then apply `finishProgram_spec` to the final four instructions that copy the result root through the destination and return locals.  This sequence gives loop completion, emitted store execution, array representation, and root transfer separate checked boundaries.

These theorems do not depend on an allocator layout or an application function.  Derive the root and payload address bounds from the allocation entry's shared `Allocation.bumpFacts`, and retain input framing through the array-memory entry when the result write occurs beside a represented input.  A wider result, dynamic result length, or nonstandard element width needs a separate result theorem or repeated use of the generic store theorems.
