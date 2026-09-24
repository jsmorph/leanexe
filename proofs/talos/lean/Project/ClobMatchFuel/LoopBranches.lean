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

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem partial_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (bounds : StepBounds ctx st data) (hFuel : data.fuel ≠ 0) (i : Nat)
    (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : ¬data.orders[i]!.oqty ≤ data.remaining)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s1 next, CompletedFacts ctx st1 s1 next →
      measure st1 s1 < measure st base →
      data.g0.toNat ≤ next.g0.toNat →
      s1.get 73 = some (.i64 next.book) → s1.get 75 = some (.i64 next.trades) →
      MemoryBelow.AllocationEffect st st1 data.g0 data.nodes next.nodes
        [next.book, next.trades] →
      wp «module» rest Q st1 s1 env) :
    wp «module» (PartialBranch.partialBranchProg ++ rest) Q st
      (Iteration.quantityFrame base data.bookOwner data.book ctx.taker data.orders i) env := by
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
    (Iteration.quantityFrame base data.bookOwner data.book ctx.taker data.orders i)
    data.book data.bookCapacity data.trades data.tradesCapacity data.remaining
    data.fuel data.g0 data.g2 data.g4 data.g5 tradeNext tradeResult ctx.taker
    data.orders data.tradeValues i data.nodes ctx.initialMem ctx.limit
  · simpa [Iteration.quantityFrame, SelectedOrder.loadFrame, Iteration.searchFrame] using hParams
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, List.length_set]
      using hLocals
  · simp [Iteration.quantityFrame, SelectedOrder.loadFrame]
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hFuelLocal
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, hLocals] using
      hOidElem
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hBook
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hTrades
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hRemainingLocal
  · simp [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, optionPayload,
      hLocals]
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, hLocals] using h73
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, hLocals] using h74
  · simp [SelectedOrder.At, Iteration.quantityFrame, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Iteration.searchLocals,
      hLocals]
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
  · exact bounds.partialAllocationLimit
  · exact facts.memoryFrame
  · exact facts.bookOwned
  · exact facts.tradesOwned
  · exact facts.global0
  · exact facts.global1
  · exact facts.global2
  · exact facts.global4
  · exact facts.global5
  · exact facts.freeList
  · intro st1 s1 newBook newBookCapacity newTrades newTradesCapacity nodes1
      g0Final hResult hBookOwned hTradesOwned hFreeList hMemoryFrame hPages hG0
      hG1 hG2 hG4 hG5 hBook48 hBook32 hBookCapacity hBookBelow hBookFree
      hTrades48 hTrades32 hTradesCapacity hTradesBelow hTradesFree hNodesBelow
      hHeapMono hHeapUpper hEffect
    have hCompleted := LoopCompletion.of_partial ctx st base data facts hFuel i hRemaining
      hFind hQty st1 s1 newBook newBookCapacity newTrades newTradesCapacity
      g0Final nodes1 hResult hBookOwned hTradesOwned hFreeList hMemoryFrame hPages
      hG0 hG1
      hG2 hG4 hG5 hBook48 hBook32 hBookCapacity hBookBelow hBookFree
      hTrades48 hTrades32 hTradesCapacity hTradesBelow hTradesFree hNodesBelow
      (hHeapUpper.trans bounds.partialAllocationLimit)
    apply hDone st1 s1 _ hCompleted
    · rw [measure_completed ⟨_, hCompleted⟩, measure_running facts]
      omega
    · exact hHeapMono
    · exact hResult.2.2.2.2.2.2.2.2.1
    · exact hResult.2.2.2.2.2.2.2.2.2
    · exact hEffect

set_option Elab.async false in
theorem full_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (data : RunningData) (facts : RunningFacts ctx st base data)
    (bounds : StepBounds ctx st data) (hFuel : data.fuel ≠ 0) (i : Nat)
    (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : data.orders[i]!.oqty ≤ data.remaining)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s1 next, RunningFacts ctx st1 s1 next →
      measure st1 s1 < measure st base →
      data.g0.toNat ≤ next.g0.toNat →
      s1.get 16 = some (.i64 next.trades) →
      (∀ floor : UInt64, 48 ≤ floor.toNat → floor.toNat ≤ data.g0.toNat →
        (∀ node ∈ data.nodes, floor.toNat + 48 ≤ node.root.toNat) →
        (data.oldTradesTracker ≠ 0 → floor.toNat + 48 ≤ data.trades.toNat) →
        MemoryBelow.BytesEqBelow st.mem st1.mem floor.toNat ∧
        (∀ root ∈ [next.book, next.trades], floor.toNat + 48 ≤ root.toNat) ∧
        (∀ node ∈ next.nodes, floor.toNat + 48 ≤ node.root.toNat)) →
      wp «module» rest Q st1 s1 env) :
    wp «module» (Iteration.fullBranchProg ++ rest) Q
      st (Iteration.quantityFrame base data.bookOwner data.book ctx.taker data.orders i) env := by
  rcases facts.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
    hTrader, hSide, hPrice, hQtyLocal, hBookOwner, hBook, hTrades, hRemainingLocal,
    hOldBook, hOldTrades, hRunning, hScratch⟩
  rcases hScratch with
    ⟨bookCapacity, bookNext, tradeNext, tradeResult, h70, h71, h73, h74⟩
  have hi : i < data.orders.length :=
    findBestL_some_lt data.orders ctx.taker i hFind
  have hOidAt : base.locals[0]? = some (.i64 ctx.taker.oid) := by
    simpa [Locals.get, hParams, hLocals] using hOid
  have hTracker :
      data.oldTradesTracker = 0 ∨ data.oldTradesTracker = data.trades := by
    by_cases hSteps : data.steps = 0
    · left
      rw [facts.oldTradesTracker]
      simp [hSteps]
    · right
      rw [facts.oldTradesTracker]
      simp [hSteps]
  apply Iteration.fullBranchProg_spec env st
    (Iteration.quantityFrame base data.bookOwner data.book ctx.taker data.orders i) data.book
    ctx.taker data.orders i
  · simpa [Iteration.quantityFrame, SelectedOrder.loadFrame, Iteration.searchFrame] using hParams
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, List.length_set]
      using hLocals
  · simp [Iteration.quantityFrame, SelectedOrder.loadFrame]
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hOid
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hTrader
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hSide
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hPrice
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hQtyLocal
  · simpa [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
      hLocals] using hBook
  · simp [Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
      SelectedOrder.loadLocals, Iteration.searchFrame, optionPayload,
      Locals.get, hParams, hLocals]
  · exact hi
  · exact bounds.ordersLength64
  · exact bounds.orderWords64
  · exact facts.bookOwned.2
  · apply FullStep.fullBookThenStep_spec env st
      (Iteration.fullPrepareFrame
        (Iteration.quantityFrame base data.bookOwner data.book ctx.taker data.orders i)
        data.book ctx.taker data.orders i)
      data.fuel data.book data.bookCapacity data.trades data.tradesCapacity
      data.remaining data.g0 data.g2 data.g4 data.g5 bookCapacity bookNext
      tradeNext data.oldTradesTracker ctx.taker data.orders data.tradeValues i
      data.nodes ctx.initialMem ctx.limit
    · simpa [Iteration.fullPrepareFrame, Iteration.quantityFrame,
        SelectedOrder.loadFrame, Iteration.searchFrame] using hParams
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, List.length_set] using
        hLocals
    · simp [Iteration.fullPrepareFrame]
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, List.getElem?_set]
        using hOidAt
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
        hLocals] using hBook
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
        hLocals] using hTrades
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
        hLocals] using hRemainingLocal
    · simp [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, optionPayload, hLocals]
    · simp [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, List.length_set,
        hLocals]
    · simp [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, List.length_set,
        hLocals]
    · simp [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, List.length_set,
        hLocals]
    · simp [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, List.length_set,
        hLocals]
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, hLocals] using h70
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, hLocals] using h71
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, hLocals] using h73
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, SelectedOrder.loadFrame, SelectedOrder.loadLocals,
        Iteration.searchFrame, Iteration.searchLocals, Locals.get, hParams, hLocals] using hFuelLocal
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
        hLocals] using hOldBook
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
        hLocals] using hOldTrades
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, Iteration.searchFrame, Locals.get, hParams,
        hLocals] using hRunning
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchFrame, Iteration.searchLocals,
        SelectedOrder.loadFrame, SelectedOrder.loadLocals, Locals.get,
        hParams, hLocals] using hOid
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchFrame, Iteration.searchLocals,
        SelectedOrder.loadFrame, SelectedOrder.loadLocals, Locals.get,
        hParams, hLocals] using hTrader
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchFrame, Iteration.searchLocals,
        SelectedOrder.loadFrame, SelectedOrder.loadLocals, Locals.get,
        hParams, hLocals] using hSide
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchFrame, Iteration.searchLocals,
        SelectedOrder.loadFrame, SelectedOrder.loadLocals, Locals.get,
        hParams, hLocals] using hPrice
    · simpa [Iteration.fullPrepareFrame, Iteration.fullPrepareLocals,
        Iteration.quantityFrame, Iteration.searchFrame, Iteration.searchLocals,
        SelectedOrder.loadFrame, SelectedOrder.loadLocals, Locals.get,
        hParams, hLocals] using hQtyLocal
    · exact hTracker
    · simp [SelectedOrder.At, Iteration.fullPrepareFrame,
        Iteration.fullPrepareLocals, Iteration.quantityFrame,
        Iteration.searchFrame, Iteration.searchLocals, SelectedOrder.loadFrame,
        SelectedOrder.loadLocals, hLocals]
    · exact hi
    · exact bounds.ordersLength64
    · exact bounds.erasedLength64
    · exact bounds.orderWords64
    · exact bounds.fullBookBytes
    · exact bounds.fullBookTop
    · exact bounds.fullBookFit32
    · exact bounds.fullBookFit
    · exact bounds.tradeLength64
    · exact bounds.tradeBytes
    · exact bounds.tradeTotalU
    · exact bounds.tradeTotal64
    · exact bounds.tradeTopAtG0
    · exact bounds.tradeFit32AtG0
    · exact bounds.tradeFitAtG0
    · exact bounds.fullTradeTopAfterBook
    · exact bounds.fullTradeFit32AfterBook
    · exact bounds.fullTradeFitAfterBook
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
    · exact bounds.fullAllocationLimit
    · exact facts.memoryFrame
    · exact facts.bookOwned
    · exact facts.tradesOwned
    · exact facts.global0
    · exact facts.global1
    · exact facts.global2
    · exact facts.global4
    · exact facts.global5
    · exact facts.freeList
    · intro st1 s1 newBook newBookCapacity newTrades newTradesCapacity nodes1
        g0Final hRecursive hScratch hBookOwned hTradesOwned hBook48 hBook32
        hBookCapacity hTrades48 hTrades32 hTradesCapacity hBookBelow hTradesBelow
        hHeapMono hHeapUpper hBookFree hTradesFree hNodesBelow hFreeList
        hMemoryFrame hPages hG0 hG1 hG2 hG4 hG5 hEffect
      let final := FullTransition.fullTransitionFrame s1 data.fuel ctx.taker
        newBook newTrades (data.remaining - data.orders[i]!.oqty) 0
        data.oldTradesTracker
      let next := LoopAdvance.nextData data ctx.taker i newBook newBookCapacity
        newTrades newTradesCapacity g0Final nodes1
      have nextFacts : RunningFacts ctx st1 final next := by
        dsimp only [final, next]
        exact LoopAdvance.of_full ctx st base data facts hFuel i hRemaining hFind
          hQty st1
          (FullTransition.fullTransitionFrame s1 data.fuel ctx.taker newBook
            newTrades (data.remaining - data.orders[i]!.oqty) 0
            data.oldTradesTracker)
          newBook newBookCapacity newTrades newTradesCapacity g0Final nodes1
          hRecursive hScratch hBookOwned hTradesOwned hBook48 hBook32 hBookCapacity
          hTrades48 hTrades32 hTradesCapacity hBookBelow hTradesBelow hHeapUpper
          hBookFree hTradesFree hNodesBelow hFreeList hMemoryFrame hPages hG0 hG1
          hG2 hG4 hG5
      have hMeasure : measure st1 final < measure st base := by
        rw [measure_running nextFacts, measure_running facts]
        simp only [next, LoopAdvance.nextData]
        rw [Budget.fuel_sub_one_toNat data.fuel hFuel]
        have hFuelPositive : 0 < data.fuel.toNat := by
          by_contra h
          have hZero : data.fuel.toNat = 0 := by omega
          apply hFuel
          apply UInt64.toNat.inj
          simpa using hZero
        omega
      apply hDone st1 final next nextFacts hMeasure hHeapMono
      · exact hRecursive.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      · exact hEffect

end Project.ClobMatchFuel.LoopBranches
