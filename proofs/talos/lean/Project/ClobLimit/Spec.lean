import Project.ClobLimit.LimitCorrect
import Project.ClobLimit.LegacyMatcher

/-!
# Specification for `clob_limit`

`LimitCorrect.func21_correct` proves termination and the exact `Model.limitL`
result for arbitrary represented order books under the stated heap, counter,
page, and allocation-budget premises. It covers invalid orders, fully filled
orders, and residual orders appended to the matched book.

The current internal function 17 uses the shared matcher invariant through a
checked local-layout transport. The proof covers its cached maker fields,
release of superseded trade arrays, reusable free list, source progress, and
strictly decreasing loop measure. `HeapCorrect.spec` proves the complete
internal function for the zero initial book owner used by this export.
`HeapRunMatch.func18_correct` composes the two empty allocations, internal call,
and exact five-value result. Globals 4 and 5 must hold UInt64 counters because
the generated cleanup reads them.

The residual append composes generic first-fit-or-bump allocation with a framed
flat-word copy and the exact five final stores. Its returned pointer is the
allocator's chosen root. The physical outcome retains owned output arrays,
exact allocator counters, free-list validity, unchanged pages, and a memory
frame. `HeapAppendOutcome.At` also preserves the matched source book and trades
through the append. The invalid branch retains its borrowed book and owned
empty trade array; the filled branch retains the shared matcher output facts.

`LegacyMatcher` preserves checked historical instruction fragments as worked
examples. They do not assert a decomposition of the current generated matcher.
-/
