import Project.ClobLimit.LimitResidualBook

namespace Project.ClobLimit.LimitResidualResult

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobLimit
  Project.ClobLimit.MatchInvariant Project.ClobLimit.LimitResidualFinishFacts
  Project.ClobMatchFuel.AllocatorFrame LimitResidualAllocation

structure ResultAt (before after : Store Unit) (ctx : Context)
    (data : MatchOutput.OutputData) (order : OrderL) : Prop where
  bookOwned : OwnedOrderArrayAt after (root ctx data) (capacity ctx data)
    (ctx.result.book ++ [{ order with oqty := ctx.result.remaining }])
  tradesOwned : OwnedTradeArrayAt after data.trades data.tradesCapacity ctx.result.trades
  pages : after.mem.pages = before.mem.pages
  globals : after.globals.globals = (allocated before ctx data).globals.globals
  memoryBelow : Project.ClobMatchFuel.MemoryBelow.BytesEqBelow before.mem after.mem ctx.initialG0.toNat

theorem of_finish (before after : Store Unit) (ctx : Context)
    (data : MatchOutput.OutputData) (order : OrderL)
    (hOutput : MatchOutput.OutputAt ctx before data)
    (hBounds : LimitResidualBounds.Facts before ctx data)
    (hFinish : FinishState (store before ctx data) after (root ctx data) (capacity ctx data)
      data.book ctx.result.book { order with oqty := ctx.result.remaining }) :
    ResultAt before after ctx data order := by
  have hTradesAlloc := LimitResidualAllocFacts.store_trades hBounds.allocation hBounds.needMin hOutput
  have hTrades := OwnedTradeArrayAt.frame_outsideFlatWords
    hOutput.trades48 hOutput.trades32 hOutput.tradesCapacity hFinish.pages
    hBounds.tradesSeparated hFinish.outside hTradesAlloc
  exact {
    bookOwned := hFinish.bookOwned
    tradesOwned := hTrades
    pages := hFinish.pages.trans (LimitResidualAllocFacts.store_pages hBounds.allocation)
    globals := hFinish.globals
    memoryBelow := (LimitResidualAllocFacts.store_memoryBelow hBounds.allocation hBounds.needMin).trans
      (Project.ClobMatchFuel.MemoryBelow.BytesEqBelow.of_outsideFlatWords
        (by have h := hBounds.allocation.rootAbove; omega) hFinish.outside) }

end Project.ClobLimit.LimitResidualResult
