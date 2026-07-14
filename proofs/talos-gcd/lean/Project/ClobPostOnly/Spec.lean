import Project.ClobPostOnly.FindBestWrapper
import Project.ClobPostOnly.ValidOrder
import Project.ClobPostOnly.Allocation
import Project.ClobPostOnly.Invalid
import Project.ClobPostOnly.Crossing

/-!
# The `postOnly` theorem

The generated artifact and its source model are pinned before the instruction
proof begins.  The primary theorem will cover invalid, crossing, and appended
outcomes for every represented input.  Each branch will state exact ownership,
allocator counters, returned arrays, and preserved memory.
-/
