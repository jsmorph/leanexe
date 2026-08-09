# Array representation across disjoint writes

Use `UInt64Array.At.frameBefore` when every changed byte begins at or above a known cutoff and the complete represented input ends at that cutoff.  The theorem preserves the array header, every element read, and the memory-page bound in one fact.  Its premises are page equality and byte equality below the cutoff.

Use `FixedArrayPairResult.input_preserved_by_alloc` for LeanExe's checked fixed-array bump allocator when the input ends below `heapTop`.  This theorem has already proved preservation across the six allocator-header writes and should precede a manual `frameBefore` proof.  Its capacity and stride arguments must match the allocator theorem applied to the exact decoded region.

Apply `UInt64Array.At.write64After` to preserve the resulting fact across a later result-length or payload store at or above the cutoff.  Normalize the store address with the allocator's shared `Allocation.bumpFacts` value, then reuse the preserved representation for length bounds, length reads, and indexed element loads.  `UInt64Array.At.generatedElement index hIndex` returns the exact modulo-address bound and memory read emitted for an in-bounds element, which avoids reconstructing the loader's address arithmetic inside a traversal loop.

Keep application-specific loop invariants and output equations outside this entry.  The represented-array facts describe memory and indexing, while a fold, map, filter, search, or tree entry supplies the semantic transition.  Demo 9 combines `generatedElement` with the generic fold-prefix invariant after preserving the input through result allocation and its length store.
