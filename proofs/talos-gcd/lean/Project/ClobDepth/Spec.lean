import Project.ClobDepth.Entry
import Project.ClobDepth.MissingBump
import Project.ClobDepth.MissingCopy
import Project.ClobDepth.MissingCopyInvariant
import Project.ClobDepth.MissingFields
import Project.ClobDepth.MissingFinish
import Project.ClobDepth.MissingPrepare
import Project.ClobDepth.MissingSearch
import Project.ClobDepth.Model
import Project.ClobDepth.Properties
import Project.ClobDepth.Program
import Project.ClobDepth.Representation
import Project.ClobDepth.Scan

/-!
# Specification for `clob_depth`

The artifact proof will relate both returned level arrays to `Model.depthL`
for every represented order book.  It will state array ownership, allocator
counters, page preservation, and the memory region preserved from the input.
The source theorems establish side filtering, first-price order, unique output
prices, exact modular aggregation, and bounded natural-number quantities.
-/

namespace Project.ClobDepth

open Wasm

end Project.ClobDepth
