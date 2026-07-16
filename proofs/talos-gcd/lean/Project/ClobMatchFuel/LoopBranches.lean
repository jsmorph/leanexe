import Project.ClobMatchFuel.LoopAdvance

/-!
# Match-loop branch composition

The dispatcher prepares branch-local frames before entering either allocation
path.  These theorems connect those frames to the physical branch theorems and
return the corresponding completed or running invariant.
-/

namespace Project.ClobMatchFuel.LoopBranches

open Wasm Project.Clob Project.Runtime Project.ClobFindBest.Model
  Project.ClobMatchFuel Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame Project.ClobMatchFuel.LoopInvariant
  Project.ClobMatchFuel.LoopBounds

set_option Elab.async false in
theorem partial_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (bounds : StepBounds ctx st data) (hFuel : data.fuel ≠ 0) (i : Nat)
    (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : ¬data.orders[i]!.oqty ≤ data.remaining)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s1, CompletedAt ctx st1 s1 →
      wp «module» rest Q st1 s1 env) :
    wp «module» (PartialBranch.partialBranchProg ++ rest) Q st
      (Iteration.quantityFrame base data.bookOwner data.book ctx.taker i) env := by
  rcases facts.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
    hTrader, hSide, hPrice, hQtyLocal, hBookOwner, hBook, hTrades, hRemainingLocal,
    hOldBook, hOldTrades, hRunning, hScratch⟩
  rcases hScratch with
    ⟨bookCapacity, bookNext, tradeNext, tradeResult, h70, h71, h73, h74⟩
  have hi : i < data.orders.length :=
    findBestL_some_lt data.orders ctx.taker i hFind
  have hOidElem : base.locals[0] = .i64 ctx.taker.oid := by
    simp only [Locals.get] at hOid
    simpa [hParams, hLocals] using hOid
  apply PartialBranch.partialBranchProg_spec env st
    (Iteration.quantityFrame base data.bookOwner data.book ctx.taker i)
    data.book data.bookCapacity data.trades data.tradesCapacity data.remaining
    data.g0 data.g2 data.g4 data.g5 tradeNext tradeResult ctx.taker data.orders
    data.tradeValues i data.nodes
  · simpa [Iteration.quantityFrame] using hParams
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, List.length_set]
      using hLocals
  · simp [Iteration.quantityFrame]
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, hLocals] using
      hOidElem
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, Locals.get, hParams,
      hLocals] using hBook
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, Locals.get, hParams,
      hLocals] using hTrades
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, Locals.get, hParams,
      hLocals] using hRemainingLocal
  · simp [Iteration.quantityFrame, Iteration.searchLocals, optionPayload,
      hLocals]
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, hLocals] using h73
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, hLocals] using h74
  · exact hi
  · exact bounds.ordersLength64
  · exact bounds.partialBookBytes
  · exact bounds.partialBookTotalU
  · exact bounds.partialBookTotal64
  · exact bounds.partialBookTop
  · exact bounds.partialBookFit32
  · exact bounds.partialBookFit
  · exact bounds.tradeLength64
  · exact bounds.tradeBytes
  · exact bounds.tradeTotalU
  · exact bounds.tradeTotal64
  · exact bounds.tradeTopAtG0
  · exact bounds.tradeFit32AtG0
  · exact bounds.tradeFitAtG0
  · exact bounds.partialTradeTopAfterBook
  · exact bounds.partialTradeFit32AfterBook
  · exact bounds.partialTradeFitAfterBook
  · exact facts.pageLimit
  · exact facts.book48
  · exact facts.book32
  · exact facts.bookCapacity
  · exact facts.bookBelow
  · exact facts.bookFree
  · exact facts.trades48
  · exact facts.trades32
  · exact facts.tradesCapacity
  · exact facts.tradesBelow
  · exact facts.tradesFree
  · exact facts.nodesBelow
  · exact facts.bookOwned
  · exact facts.tradesOwned
  · exact facts.global0
  · exact facts.global1
  · exact facts.global2
  · exact facts.global4
  · exact facts.global5
  · exact facts.freeList
  · intro st1 s1 newBook newBookCapacity newTrades newTradesCapacity nodes1
      g0Final hResult hBookOwned hTradesOwned hFreeList hG0 hG1 hG2 hG4 hG5
    apply hDone st1 s1
    exact LoopCompletion.of_partial ctx st base data facts hFuel i hRemaining
      hFind hQty st1 s1 newBook newBookCapacity newTrades newTradesCapacity
      g0Final nodes1 hResult hBookOwned hTradesOwned hFreeList hG0 hG1 hG2 hG4
      hG5

end Project.ClobMatchFuel.LoopBranches
