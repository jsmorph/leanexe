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
