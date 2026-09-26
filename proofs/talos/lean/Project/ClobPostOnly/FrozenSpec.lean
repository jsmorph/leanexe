import Project.ClobPostOnly.FrozenFindBestWrapper
import Project.ClobPostOnly.FrozenValidOrder
import Project.ClobPostOnly.FrozenAllocation
import Project.ClobPostOnly.FrozenInvalid
import Project.ClobPostOnly.FrozenCrossing
import Project.ClobPostOnly.FrozenAppend

/-!
# The `postOnly` theorem

The generated artifact and its source model are pinned before the instruction
proof begins.  Three input-generic theorems cover invalid, crossing, and
appended outcomes for every represented input under their stated bounds.  Each
branch states exact ownership, allocator counters, returned arrays, and
preserved memory.
-/
