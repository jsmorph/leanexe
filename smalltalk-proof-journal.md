# Smalltalk proof journal

## Concrete memory and allocation (2026-10-06)

The earlier Smalltalk proofs describe separate lists; they do not justify the
array implementation. `Project.Smalltalk.Memory` now checks read-after-write,
unchanged reads at other indices, and the address arithmetic used by the VM.
The capacity limit and positive handle bound are explicit: without those bounds
UInt64 subtraction and addition can wrap. The first arithmetic attempt omitted
the handle upper bound from the local arithmetic facts and failed. Naming that
bound lets `omega` prove both intermediate products and final addresses are
smaller than 2^64. The core array lemmas suffice; no imported WASM proof is
needed.

`allocateCell_read` checks the complete write sequence against a separate
word-level postcondition. `allocateCell_field` then proves exactly what the
new cell contains, and `allocateCell_preserves_other` proves all eight words of
every other valid cell are unchanged. `allocateCell_register` and
`allocateCell_shape` check the register effects and unchanged arena layout.
The shared address equality lemma avoids repeating UInt64 arithmetic in these
proofs. Enumerating the eight possible offsets required converting word
equalities to Nat equalities before `omega`; asking it to derive the word
disjunction directly failed.

These results assume a valid free-head handle. They do not establish free-list
membership or count, collector reachability, VM instruction semantics, or WASM
correctness. The Smalltalk driver now builds the proof imports and reports
axioms for the main concrete theorems before running the existing execution
checks.

## Free-list allocation (2026-10-06)

`FreeList.Chain` records the concrete next word of each free cell, valid
handles, and distinct membership. `FreeList.Valid` additionally requires the
actual count and exact agreement between zero tags and list membership.
`allocate_valid` now proves that the checked allocator preserves shape and
this complete free-list invariant while removing one head. Allocating a zero
tag is excluded explicitly; otherwise completeness would be false.
`allocate_empty_preserves_cells` checks the error path and proves that all
cell words remain unchanged when the valid list is empty.

Direct case analysis on a chain indexed by `read s 8` failed because dependent
elimination attempted to resolve the array read against zero. The generic
`chain_cons` and `chain_nil` inversion lemmas avoid that problem. The previously
checked cell-preservation and register-effect lemmas then suffice for the
allocation proof; no executable definition changed. These theorems assume
free-list validity before allocation. Initialization and collection still
need proofs that establish it.

## Complete sweep (2026-10-06)

`reclaim_read`, `reclaim_field`, and `reclaim_register` check the actual writes
made by reclamation. The collector's sweep preserves mark words and arena
shape. `finishCollection_preserves_marked` applies an invariant through the
actual bounded loop and proves that all eight words of each marked cell remain
unchanged, including after the final statistics write.

`SweepList.Prefix` records precisely which unmarked handles have been visited,
the concrete linked list, its count, unchanged mark words, and a count bound
that rules out integer wraparound. `counted_index` establishes that the loop
visits all handles through capacity. `finishCollection_freeList` then proves
that the result has a complete free list containing exactly the original
unmarked handles, each once. It assumes marked cells have nonzero tags; this
is the condition the marking proof must supply.

The initial audit permitted only `propext` and `Quot.sound`. The new arithmetic
proofs also use `Classical.choice` through generated `omega` proof terms. The
audit now permits these three standard Lean axioms and still rejects every
other axiom, including `sorryAx`. This is recorded in the public proof limits;
the executable implementation and its tests are unchanged. The sweep theorem
does not establish reachability or correctness of the full `collect` call.
