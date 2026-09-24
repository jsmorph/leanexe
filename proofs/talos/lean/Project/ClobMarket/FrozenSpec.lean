import Project.ClobMarket.FrozenModel
import Project.ClobMarket.FrozenProgram
import Project.ClobMarket.FrozenMatchRegion
import Project.ClobMarket.FrozenRunMatch
import Project.ClobMarket.FrozenExportRegion
import Project.ClobMarket.FrozenHelpers
import Project.ClobMarket.FrozenEntry
import Project.ClobMarket.FrozenValidEntry
import Project.ClobMarket.FrozenInvalidEntry
import Project.ClobMarket.FrozenInvalidPrepare
import Project.ClobMarket.FrozenInvalidSearch
import Project.ClobMarket.FrozenInvalidBump
import Project.ClobMarket.FrozenInvalidFinish
import Project.ClobMarket.FrozenInvalidPost
import Project.ClobMarket.FrozenInvalidProgram
import Project.ClobMarket.FrozenInvalidResult
import Project.ClobMarket.FrozenInvalid
import Project.ClobMarket.FrozenPrice
import Project.ClobMarket.FrozenCall
import Project.ClobMarket.FrozenValidResult
import Project.ClobMarket.FrozenValid
import Project.ClobMarket.FrozenCorrect

/-!
# Specification for `clob_market`

The artifact proof relates the exported function to `Model.marketL` for every
represented input.  Its branch theorems state result ownership, allocator
counters, page preservation, and a budgeted memory frame.  The aggregate proof
library imports this completed specification.

The seven-function matcher region is definitionally equal to the completed
limit region.  Its certificate transports the complete function 18 theorem,
including owned result arrays and exact allocator and memory facts.  The
exported function 21 proof composes that result with its validity branches.

The valid exported branch proves the exact unlimited-price transformation,
transports function 18, and returns its represented book and trades with status
zero.  The invalid branch proves the exact status, borrowed book, owned empty
trade array, allocator globals, page count, and memory frame.  The primary
theorem relates both branches to `Model.marketL` and retains their physical
outcomes.
-/

namespace Project.ClobMarket.Frozen

open Wasm

end Project.ClobMarket.Frozen
