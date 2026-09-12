# Fixed-array bump allocation with growth

`FixedArrayBump.program_spec` composes address preparation, the overflow
guard, required-page calculation, conditional memory growth, heap-top
and result-root assignment, and the six fixed-array header stores.
The module, frame, element stride, and four local slots are parameters.
The theorem requires the non-parameter slots in need/top/pages/result
order.  Its result names the exact store and frame.

The theorem applies to the bump branch after allocator search selects
no reusable node.  Search remains an enclosing proof obligation.  The
branch theorem does not constrain the free-list global because the
branch preserves it.  `requiredPages_le`, `requiredPages_word`, and
`requiredPages_fit` connect the checked address arithmetic to
`MemoryGrowth.ensureProgram_spec`.  `FixedArrayHeader.program_spec`
discharges the bounded metadata stores.

The prefix and installation theorems checked in 3.2 and 3.3 seconds,
and the complete composition in 2.1 seconds.  All public audits use
standard axioms.  The installation proof keeps the result frame named
through the preserved-local read before reducing its record projections.
Premature frame reduction prevented the getter rewrite in the failed
draft.

Riemann initialization checks exact branch equalities for capacity
locals 54, 59, and 60, with top/pages/result at offsets three, four, and
five.  The last layout appears in both extraction paths.  The four
matches and their common execution theorem checked in 3.6 seconds.
These sites have five parameters and may require memory growth.
The earlier allocator-window theorem requires one parameter, an empty
free list, and enough existing memory.  Its premises remain unchanged.

The entry remains provisional pending complete allocation-search and
artifact consumers and independent package verification.
