import Project.ClobLimit.LimitResidualBook

/-!
# Residual result state

The residual book writes preserve the matcher-produced trade array and memory
below the matcher heap top.  This module converts the internal finish predicate
into the physical result stated by the exported branch theorem.
-/

namespace Project.ClobLimit.LimitResidualResult

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobLimit.LimitResidualFinishFacts
  Project.ClobLimit.LimitResidualBounds
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

structure ResultAt (before after : Store Unit) (ctx : Context)
    (data : InternalLoopResult.OutputData) (order : OrderL) : Prop where
  bookOwned : OwnedOrderArrayAt after (data.g0 + 48)
    (orderArrayBytesU (ctx.result.book.length + 1))
    (ctx.result.book ++ [{ order with oqty := ctx.result.remaining }])
  tradesOwned : OwnedTradeArrayAt after data.trades data.tradesCapacity
    ctx.result.trades
  pages : after.mem.pages = before.mem.pages
  globals : after.globals.globals =
    ((before.globals.globals.set 0
      (.i64 (data.g0 + 48 +
        orderArrayBytesU (ctx.result.book.length + 1)))).set 2
      (.i64 (ctx.expectedG2 + 1)))
  memoryBelow : BytesEqBelow before.mem after.mem data.g0.toNat

theorem of_finish
    (before after : Store Unit) (ctx : Context)
    (data : InternalLoopResult.OutputData) (order : OrderL)
    (hLength : ctx.result.book.length + 1 < UInt64.size)
    (hBytes : orderArrayBytes (ctx.result.book.length + 1) + 7 <
      UInt64.size)
    (hFit32 : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat < 4294967296)
    (hFit : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat <=
        before.mem.pages * 65536)
    (hOutput : InternalLoopResult.OutputAt ctx before data)
    (hFinish : FinishState
      (LimitResidualAlloc.allocStore before data.g0 ctx.expectedG2
        (orderArrayBytesU (ctx.result.book.length + 1))
        (UInt64.ofNat (ctx.result.book.length + 1)))
      after data.g0 (orderArrayBytesU (ctx.result.book.length + 1))
      data.book ctx.result.book
      { order with oqty := ctx.result.remaining }) :
    ResultAt before after ctx data order := by
  have hBounds := LimitResidualBounds.derive before ctx data hLength hBytes
    hFit32 hFit hOutput
  have hTradesAlloc :=
    LimitResidualAllocFacts.ownedTradeArrayAt_allocStore
      (st := before) (g0 := data.g0) (g2 := ctx.expectedG2)
      (need := orderArrayBytesU (ctx.result.book.length + 1))
      (length := UInt64.ofNat (ctx.result.book.length + 1))
      (source := data.trades) (sourceCapacity := data.tradesCapacity)
      (ts := ctx.result.trades) hBounds.needMin hFit32 hBounds.targetNat
      hOutput.trades48 hOutput.trades32 hOutput.tradesCapacity
      hOutput.tradesBelow hOutput.tradesOwned
  have hSeparated : regionsDisjoint
      (flatWordsRegion (data.g0 + 48)
        ((ctx.result.book.length + 1) * 5))
      (fixedArrayRegion data.trades data.tradesCapacity) := by
    unfold regionsDisjoint flatWordsRegion fixedArrayRegion
    right
    have hTrades48 := hOutput.trades48
    have hTradesBelow := hOutput.tradesBelow
    rw [hBounds.targetNat]
    omega
  have hTrades := OwnedTradeArrayAt.frame_outsideFlatWords
    hOutput.trades48 hOutput.trades32 hOutput.tradesCapacity hFinish.pages
    hSeparated hFinish.outside hTradesAlloc
  exact {
    bookOwned := hFinish.bookOwned
    tradesOwned := hTrades
    pages := by
      rw [hFinish.pages, LimitResidualAllocFacts.allocStore_pages]
    globals := by
      rw [hFinish.globals, LimitResidualAllocFacts.allocStore_globals]
    memoryBelow := by
      intro a ha
      calc
        after.mem.bytes a =
            (LimitResidualAlloc.allocStore before data.g0 ctx.expectedG2
              (orderArrayBytesU (ctx.result.book.length + 1))
              (UInt64.ofNat
                (ctx.result.book.length + 1))).mem.bytes a :=
          hFinish.outside a (Or.inl (by rw [hBounds.targetNat]; omega))
        _ = before.mem.bytes a :=
          LimitResidualAllocFacts.allocStore_bytes_before before data.g0
            ctx.expectedG2
            (orderArrayBytesU (ctx.result.book.length + 1))
            (UInt64.ofNat (ctx.result.book.length + 1)) a hBounds.needMin
            hFit32 hBounds.targetNat ha }

end Project.ClobLimit.LimitResidualResult
