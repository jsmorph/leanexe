import Project.ClobDepth.Model
import Project.ClobDepth.Program

/-!
# Specification for `clob_depth`

The artifact proof will relate both returned level arrays to `Model.depthL`
for every represented order book.  It will state array ownership, allocator
counters, page preservation, and the memory region preserved from the input.
The source properties will cover side filtering, first-price order, and
modular and bounded natural-number quantity totals.
-/

namespace Project.ClobDepth

open Wasm

end Project.ClobDepth
