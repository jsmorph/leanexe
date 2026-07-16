import Project.ClobMatchFuel.EarlyExit
import Project.ClobMatchFuel.BookEraseSuffix
import Project.ClobMatchFuel.BookReplaceFinish
import Project.ClobMatchFuel.BookAlloc
import Project.ClobMatchFuel.BookAllocErase
import Project.ClobMatchFuel.PartialBookAlloc
import Project.ClobMatchFuel.PartialBookAllocCopy
import Project.ClobMatchFuel.PartialBookUpdate
import Project.ClobMatchFuel.PartialBookPrepare
import Project.ClobMatchFuel.TradeAlloc
import Project.ClobMatchFuel.TradeAllocCopy
import Project.ClobMatchFuel.TradeAllocAppend
import Project.ClobMatchFuel.PartialTradePrepare
import Project.ClobMatchFuel.TradeAppendCopy
import Project.ClobMatchFuel.TradeAppendFinish
import Project.ClobMatchFuel.FullTradePrepare
import Project.ClobMatchFuel.FullTradeFinish
import Project.ClobMatchFuel.ReleaseOld
import Project.ClobMatchFuel.FullTransition

/-!
# The `matchFuel` theorem

The generated artifact and its source model are the proof subjects for bounded
order matching.  The primary theorem will relate the recursive export to exact
book, trade, and remaining-quantity results for every represented input.  Its
proof will state returned ownership, allocator counters, and preserved memory
for each update branch.
-/
