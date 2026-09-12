# Fixed-array allocation after an undersized free list

`FixedArraySearch.noneProgram_spec` proves the complete block-wrapped
search under a represented free list and `takeFirstFit need nodes = none`.
It preserves the exact store.  Its six scratch slots contain need,
previous, current, capacity, next, and result, with arbitrary parameter,
saved-local, and trailing-local lists.  The fit branch is an arbitrary
program because the capacity premise excludes its execution.

The invariant records a visited/remaining decomposition, the represented
remaining list, and the fact that every remaining capacity is too small.
The existing `FreeListAt.scanRemaining_suffix` theorem proves strict
decrease.  Shared field-read and pointer-advance theorems discharge each
iteration, including memory bounds.  The search exits with current and
result equal to zero and preserves every surrounding local.

`FixedArraySearch.frame_get_before` identifies every parameter or
saved-local getter before the scratch window with the unchanged prefix
frame.  The initializer heap-allocation theorem uses it to return
explicit getter preservation for all three emitted layouts.  The
shared projection checked in 40 seconds and the consumer in 50 seconds,
with standard axioms.  The first projection draft left an equivalent
expanded list-length bound, which the corrected proof closes with omega.

`noneRegion_spec` accepts an explicit equality from the emitted loop
body to the shared search body.  It transports that equality with an
arbitrary module before a consumer supplies its concrete module.

`FixedArrayAllocateNone.program_spec` adds search initialization, the
guarded bump branch, and allocation counting.  It composes
`FixedArrayBump.program_spec` for conditional memory growth and exact
header writes.  The continuation receives the exact resulting store and
the computed top, page count, and root.  The theorem requires the heap,
free-list, and count globals, a 32-bit fit bound, and enough runtime
memory capacity.

Keep the canonical frame as `saved ++ (sixLocals ++ tail)`.
This association agrees with the WP local operations.  Preserve named
frames until getter equalities have rewritten, and normalize local-index
addition before applying the bump-result projection.

The shared field-read and advance proofs checked in 1.8 seconds, the
complete search in 2.4 seconds, and the allocation composition in 69
seconds.  Every public audit uses standard axioms.  The first composition
draft failed on addition association at its result-frame rewrite.
Riemann initialization supplies three distinct scratch starts, 54, 59,
and 60, with the final layout used by both extraction paths.  Its exact
region equalities checked in 58 seconds and the common execution
consumer in 56 seconds.  The entry is
provisional pending complete initializer and independent artifact
verification.

These build durations include imports and system I/O.  A subsequent
100-second check of the region adapter coincided with memory pressure
and a 23.49-percent 60-second system full-I/O-stall average.  The
measurements do not isolate elaboration cost or establish a performance
improvement.

The Riemann map-data consumer composes pointer installation, the length
store, counter initialization, and the checked map loop.  Its bounded
write range then composes with existing heap-allocation bounds and
source-owner preservation to establish both live-grid owners.  The
map-data proof checked in 63 seconds and ownership composition in 41
seconds with standard axioms.  The complete initializer and independent
artifact verification remain pending.

`FixedArraySearch.resultFrame_before` rewrites an assignment before the
scratch window as an update of the saved-local list.
`capacityFrame_need` replaces the first scratch word with the prepared
capacity.  Both equalities preserve arbitrary surrounding locals and
the other five scratch words.  They checked in 32 seconds with standard
axioms.  Apply `Frame.ext` to the goal before supplying its field
equalities: elaborating two unspecified frames with immediate `rfl`
arguments identified them prematurely in the first failed draft.
The initializer map's input and capacity frame equalities use both
declarations and checked in 34 seconds.  Its getter conjunction uses
the shared assignment theorem explicitly after removing intervening
writes, because simplification left the valid-index premises open.
