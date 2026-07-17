import Project.ClobMarket.Model
import Project.ClobMarket.Program
import Project.ClobMarket.MatchRegion
import Project.ClobMarket.RunMatch

/-!
# Specification for `clob_market`

The artifact proof will relate the exported function to `Model.marketL` for
every represented input.  Its branch theorems will state result ownership,
allocator counters, page preservation, and a budgeted memory frame.  This
module remains outside `Project.lean` until those theorems are complete.

The seven-function matcher region is definitionally equal to the completed
limit region.  Its certificate transports the complete function 18 theorem,
including owned result arrays and exact allocator and memory facts.  The
remaining proof covers exported function 21 only.
-/

namespace Project.ClobMarket

open Wasm

end Project.ClobMarket
