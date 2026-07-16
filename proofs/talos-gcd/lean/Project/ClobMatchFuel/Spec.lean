import Project.ClobMatchFuel.EarlyExit
import Project.ClobMatchFuel.BookEraseSuffix
import Project.ClobMatchFuel.BookReplaceFinish
import Project.ClobMatchFuel.BookAlloc
import Project.ClobMatchFuel.BookAllocErase
import Project.ClobMatchFuel.FullBookUpdate
import Project.ClobMatchFuel.PartialBookAlloc
import Project.ClobMatchFuel.PartialBookAllocCopy
import Project.ClobMatchFuel.PartialBookUpdate
import Project.ClobMatchFuel.PartialBookPrepare
import Project.ClobMatchFuel.TradeAlloc
import Project.ClobMatchFuel.TradeAllocCopy
import Project.ClobMatchFuel.TradeAllocAppend
import Project.ClobMatchFuel.PartialTradePrepare
import Project.ClobMatchFuel.PartialFinish
import Project.ClobMatchFuel.PartialTradeUpdate
import Project.ClobMatchFuel.PartialBranch
import Project.ClobMatchFuel.TradeAppendCopy
import Project.ClobMatchFuel.TradeAppendFinish
import Project.ClobMatchFuel.FullTradePrepare
import Project.ClobMatchFuel.FullTradeFinish
import Project.ClobMatchFuel.FullTradeUpdate
import Project.ClobMatchFuel.FullBranch
import Project.ClobMatchFuel.ReleaseOld
import Project.ClobMatchFuel.FullTransition
import Project.ClobMatchFuel.FullReleaseTransition
import Project.ClobMatchFuel.FullStep
import Project.ClobMatchFuel.LoopControl
import Project.ClobMatchFuel.Iteration
import Project.ClobMatchFuel.LoopInvariant
import Project.ClobMatchFuel.LoopBounds
import Project.ClobMatchFuel.LoopProgress
import Project.ClobMatchFuel.LoopCompletion
import Project.ClobMatchFuel.LoopAdvance
import Project.ClobMatchFuel.LoopBranches

/-!
# The `matchFuel` theorem

The generated artifact and its source model are the proof subjects for bounded
order matching.  The primary theorem will relate the recursive export to exact
book, trade, and remaining-quantity results for every represented input.  Its
proof will state returned ownership, allocator counters, and preserved memory
for each update branch.
-/
