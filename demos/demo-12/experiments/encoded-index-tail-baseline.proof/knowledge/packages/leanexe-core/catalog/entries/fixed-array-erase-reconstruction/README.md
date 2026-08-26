# UInt64 array erase reconstruction

Use `UInt64Array.At.eraseIdx!_of_reads` after the artifact proof has executed allocation, the result-length store, the prefix-copy loop, and the shifted-suffix loop.  The theorem accepts a represented source array in one store and target read equations in another store, so the artifact proof can describe the final bytes without preserving the source representation in the final store.  It concludes that the target pointer represents `input.eraseIdx! erase` under the public `Array UInt64` ABI.

Supply the in-bounds erase index, target bounds, and target length read first.  State the prefix premise for result indices `j < erase`, where the target read equals the source read at `j`.  State the suffix premise for `erase ≤ j < input.size - 1`, where the target read equals the source read at `j + 1`; the theorem applies Lean's checked `Array.getElem_eraseIdx_of_lt` and `Array.getElem_eraseIdx_of_ge` equations.

This declaration reconstructs representation from established reads.  Allocation semantics, ownership, source preservation during machine execution, and both copy loops remain separate proof obligations.  It covers flat one-word `UInt64` elements and an in-bounds erase, while the no-match path can return the represented input without invoking this theorem.
