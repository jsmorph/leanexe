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
import Project.ClobMarket.Price
import Project.ClobMarket.Call
import Project.ClobMarket.ValidResult
import Project.ClobMarket.Valid

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

The valid exported branch proves the exact unlimited-price transformation,
transports function 18, and returns its represented book and trades with status
zero.  The invalid branch now proves validity entry, allocator preparation,
empty free-list search, and the fixed-array header and heap-top writes.  The
length store, counter update, branch theorem, and primary theorem remain.
-/

namespace Project.ClobMarket

open Wasm

end Project.ClobMarket
