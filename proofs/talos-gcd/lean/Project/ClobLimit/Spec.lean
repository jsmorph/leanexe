import Project.ClobLimit.Model
import Project.ClobLimit.Program
import Project.ClobLimit.ValidOrder
import Project.ClobLimit.Invalid
import Project.ClobLimit.FindBestWrapper
import Project.ClobLimit.InternalEarlyExit

/-!
# Specification for `clob_limit`
-/

namespace Project.ClobLimit

open Wasm

/-!
The artifact proof will relate exported function 21 to `Model.limitL` for every
represented input.  Its branch theorems will state result ownership, allocator
counters, page preservation, and a budgeted memory frame.  The validity,
invalid-result, embedded search, and internal early-exit subsystems are
complete.  This module remains outside `Project.lean` until the exported
theorem is complete.
-/

end Project.ClobLimit
