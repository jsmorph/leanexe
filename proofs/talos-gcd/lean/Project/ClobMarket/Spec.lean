import Project.ClobMarket.Model
import Project.ClobMarket.Program
import Project.ClobMarket.MatchRegion
import Project.ClobMarket.RunMatch
import Project.ClobMarket.ExportRegion
import Project.ClobMarket.Helpers
import Project.ClobMarket.Entry
import Project.ClobMarket.ValidEntry
import Project.ClobMarket.InvalidEntry
import Project.ClobMarket.InvalidPrepare
import Project.ClobMarket.InvalidSearch
import Project.ClobMarket.InvalidBump
import Project.ClobMarket.InvalidFinish
import Project.ClobMarket.InvalidPost
import Project.ClobMarket.InvalidProgram
import Project.ClobMarket.InvalidResult
import Project.ClobMarket.Invalid
import Project.ClobMarket.Price
import Project.ClobMarket.Call
import Project.ClobMarket.ValidResult
import Project.ClobMarket.Valid
import Project.ClobMarket.Correct

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

namespace Project.ClobMarket

open Wasm

end Project.ClobMarket
