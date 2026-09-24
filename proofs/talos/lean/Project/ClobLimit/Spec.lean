import Project.ClobLimit.LimitCorrect

/-!
# Specification for `clob_limit`

`LimitCorrect.func21_correct` proves termination and exact agreement with
`Model.limitL` for represented inputs under its allocation budget.  Its three
outcomes cover invalid orders, filled orders, and insertion of a residual order.
Each outcome retains the corresponding ownership and allocator facts, unchanged
pages, and preservation of memory below the caller's initial heap boundary.

The internal matcher reuses the checked matching branches through function and
local-variable renaming.  Its loop tracks returned owners, released trade
buffers, and the free list.  Residual insertion either reuses a suitable free
buffer or advances the heap, then copies the book and appends the remaining
order.  The exported postcondition retains that exact allocator transition.
-/
