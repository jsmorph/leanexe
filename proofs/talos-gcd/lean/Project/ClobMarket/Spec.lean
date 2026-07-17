import Project.ClobMarket.Model
import Project.ClobMarket.Program

/-!
# Specification for `clob_market`

The artifact proof will relate the exported function to `Model.marketL` for
every represented input.  Its branch theorems will state result ownership,
allocator counters, page preservation, and a budgeted memory frame.  This
module remains outside `Project.lean` until those theorems are complete.
-/

namespace Project.ClobMarket

open Wasm

end Project.ClobMarket
