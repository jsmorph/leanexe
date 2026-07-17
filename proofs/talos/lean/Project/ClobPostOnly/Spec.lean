import Project.ClobPostOnly.FindBestWrapper
import Project.ClobPostOnly.ValidOrder
import Project.ClobPostOnly.Allocation
import Project.ClobPostOnly.Invalid
import Project.ClobPostOnly.Crossing
import Project.ClobPostOnly.Append

/-!
# The `postOnly` theorem

The generated artifact and its source model are pinned before the instruction
proof begins.  Three input-generic theorems cover invalid, crossing, and
appended outcomes for every represented input under their stated bounds.  Each
branch states exact ownership, allocator counters, returned arrays, and
preserved memory.
-/
