import Project.ClobMatchFuel.FrozenEarlyExit
import Project.ClobMatchFuel.FrozenBookEraseSuffix
import Project.ClobMatchFuel.FrozenBookReplaceFinish
import Project.ClobMatchFuel.FrozenBookAlloc
import Project.ClobMatchFuel.FrozenBookAllocErase
import Project.ClobMatchFuel.FrozenFullBookUpdate
import Project.ClobMatchFuel.FrozenPartialBookAlloc
import Project.ClobMatchFuel.FrozenPartialBookAllocCopy
import Project.ClobMatchFuel.FrozenPartialBookUpdate
import Project.ClobMatchFuel.FrozenPartialBookPrepare
import Project.ClobMatchFuel.FrozenBranchPost
import Project.ClobMatchFuel.FrozenPartialBookControl
import Project.ClobMatchFuel.FrozenTradeAlloc
import Project.ClobMatchFuel.FrozenTradeAllocCopy
import Project.ClobMatchFuel.FrozenTradeAllocAppend
import Project.ClobMatchFuel.FrozenPartialTradePrepare
import Project.ClobMatchFuel.FrozenPartialFinish
import Project.ClobMatchFuel.FrozenPartialTradeUpdate
import Project.ClobMatchFuel.FrozenPartialBranch
import Project.ClobMatchFuel.FrozenTradeAppendCopy
import Project.ClobMatchFuel.FrozenTradeAppendFinish
import Project.ClobMatchFuel.FrozenFullTradePrepare
import Project.ClobMatchFuel.FrozenFullTradeFinish
import Project.ClobMatchFuel.FrozenFullTradeUpdate
import Project.ClobMatchFuel.FrozenFullBranch
import Project.ClobMatchFuel.FrozenReleaseOld
import Project.ClobMatchFuel.FrozenFullTransition
import Project.ClobMatchFuel.FrozenFullReleaseTransition
import Project.ClobMatchFuel.FrozenFullStep
import Project.ClobMatchFuel.FrozenLoopControl
import Project.ClobMatchFuel.FrozenIteration
import Project.ClobMatchFuel.FrozenLoopInvariant
import Project.ClobMatchFuel.FrozenLoopBounds
import Project.ClobMatchFuel.FrozenLoopProgress
import Project.ClobMatchFuel.FrozenLoopCompletion
import Project.ClobMatchFuel.FrozenLoopAdvance
import Project.ClobMatchFuel.FrozenLoopBranches
import Project.ClobMatchFuel.FrozenLoopIteration
import Project.ClobMatchFuel.FrozenLoop
import Project.ClobMatchFuel.FrozenLoopInitial
import Project.ClobMatchFuel.FrozenLoopResult
import Project.ClobMatchFuel.FrozenEntry
import Project.ClobMatchFuel.FrozenProperties
import Project.ClobMatchFuel.FrozenCorrect

/-!
# The `matchFuel` theorem

The generated artifact and its source model are the proof subjects for bounded
order matching.  The primary theorem relates the recursive export to exact
book, trade, and remaining-quantity results for every represented input.  It
also states returned ownership, allocator counters, page preservation, and byte
preservation above the reserved heap boundary.

`Properties.matchFuelL_steps` decomposes every source result into exact full-
or partial-fill steps.  `Properties.matchFuelL_quantity_conservation` proves
maker and taker quantity conservation against the accumulated trade quantity.
These source theorems apply directly to the artifact theorem's exact result.
-/
