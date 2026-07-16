import Project.ClobMatchFuel.LoopCompletion

/-!
# Match-loop full-fill advancement

A full fill replaces both arrays, may release the prior trade array, and
decrements fuel.  This module combines the physical full-step result with the
source-progress and budget lemmas to reconstruct the running invariant.
-/

namespace Project.ClobMatchFuel.LoopAdvance

open Wasm Project.Clob Project.Runtime Project.ClobFindBest.Model
  Project.ClobMatchFuel Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame Project.ClobMatchFuel.LoopInvariant
  Project.ClobMatchFuel.LoopProgress

def nextData (data : RunningData) (taker : OrderL) (i : Nat)
    (newBook newBookCapacity newTrades newTradesCapacity g0Final : UInt64)
    (nodes1 : List FreeNode) : RunningData :=
  { steps := data.steps + 1
    fuel := data.fuel - 1
    bookOwner := newBook
    book := newBook
    bookCapacity := newBookCapacity
    trades := newTrades
    tradesCapacity := newTradesCapacity
    remaining := data.remaining - data.orders[i]!.oqty
    oldTradesTracker := newTrades
    g0 := g0Final
    g2 := data.g2 + 2
    g4 := data.g4 + FullStep.releaseCount data.oldTradesTracker
    g5 := data.g5 + FullStep.releaseCount data.oldTradesTracker
    orders := data.orders.eraseIdx i
    tradeValues := data.tradeValues ++
      [Model.fillTradeL taker data.orders[i]! data.orders[i]!.oqty]
    nodes := nodes1 }

theorem of_full (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : data.orders[i]!.oqty ≤ data.remaining)
    (st1 : Store Unit) (s1 : Locals)
    (newBook newBookCapacity newTrades newTradesCapacity g0Final : UInt64)
    (nodes1 : List FreeNode)
    (hRecursive : FullStep.RecursiveResultAt s1 data.fuel ctx.taker newBook
      newTrades (data.remaining - data.orders[i]!.oqty))
    (hScratch : FullTradeUpdate.AllocScratchAt s1)
    (hBookOwned : OwnedOrderArrayAt st1 newBook newBookCapacity
      (data.orders.eraseIdx i))
    (hTradesOwned : OwnedTradeArrayAt st1 newTrades newTradesCapacity
      (data.tradeValues ++
        [Model.fillTradeL ctx.taker data.orders[i]! data.orders[i]!.oqty]))
    (hBook48 : 48 ≤ newBook.toNat)
    (hBook32 : newBook.toNat +
      fixedArrayBytes (data.orders.eraseIdx i).length 5 < 4294967296)
    (hBookCapacity :
      fixedArrayBytes (data.orders.eraseIdx i).length 5 ≤ newBookCapacity.toNat)
    (hTrades48 : 48 ≤ newTrades.toNat)
    (hTrades32 : newTrades.toNat + fixedArrayBytes
      (data.tradeValues ++
        [Model.fillTradeL ctx.taker data.orders[i]! data.orders[i]!.oqty]).length
      4 < 4294967296)
    (hTradesCapacity : fixedArrayBytes
      (data.tradeValues ++
        [Model.fillTradeL ctx.taker data.orders[i]! data.orders[i]!.oqty]).length
      4 ≤ newTradesCapacity.toNat)
    (hBookBelow : newBook.toNat + newBookCapacity.toNat ≤ g0Final.toNat)
    (hTradesBelow : newTrades.toNat + newTradesCapacity.toNat ≤ g0Final.toNat)
    (hHeapUpper : g0Final.toNat ≤ data.g0.toNat + 96 +
      orderArrayBytes (data.orders.length - 1) +
      tradeArrayBytes (data.tradeValues.length + 1))
    (hBookFree :
      FreeListSeparatedFromFixedArray nodes1 newBook newBookCapacity)
    (hTradesFree :
      FreeListSeparatedFromFixedArray nodes1 newTrades newTradesCapacity)
    (hNodesBelow : ∀ node ∈ nodes1,
      node.root.toNat + node.capacity.toNat ≤ g0Final.toNat)
    (hFreeList : FreeListAt st1.mem nodes1)
    (hPages : st1.mem.pages = st.mem.pages)
    (hG0 : st1.globals.globals[0]? = some (.i64 g0Final))
    (hG1 : st1.globals.globals[1]? = some (.i64 (freeHead nodes1)))
    (hG2 : st1.globals.globals[2]? = some (.i64 (data.g2 + 2)))
    (hG4 : st1.globals.globals[4]? = some
      (.i64 (data.g4 + FullStep.releaseCount data.oldTradesTracker)))
    (hG5 : st1.globals.globals[5]? = some
      (.i64 (data.g5 + FullStep.releaseCount data.oldTradesTracker))) :
    RunningFacts ctx st1 s1
      (nextData data ctx.taker i newBook newBookCapacity newTrades
        newTradesCapacity g0Final nodes1) := by
  have hi : i < data.orders.length :=
    findBestL_some_lt data.orders ctx.taker i hFind
  obtain ⟨hSource, hFills⟩ := full_source ctx st s data facts hFuel i
    hRemaining hFind hQty
  have hFuelSpent := facts.fuelSpent
  have hTradeLimit : data.tradeValues.length + 1 ≤ ctx.tradeLimit := by
    rw [facts.tradeLength]
    unfold Context.tradeLimit
    have hFuelPositive : 0 < data.fuel.toNat := by
      by_contra h
      have hZero : data.fuel.toNat = 0 := by omega
      apply hFuel
      apply UInt64.toNat.inj
      simpa using hZero
    omega
  have hTradesNe : data.trades ≠ 0 := by
    intro hZero
    have hTrades48 := facts.trades48
    rw [hZero] at hTrades48
    simp at hTrades48
  have hRelease : FullStep.releaseCount data.oldTradesTracker =
      if data.steps = 0 then 0 else 1 := by
    rw [facts.oldTradesTracker]
    by_cases hSteps : data.steps = 0
    · simp [hSteps, FullStep.releaseCount]
    · simp [hSteps, FullStep.releaseCount, hTradesNe]
  have hBudget := Budget.spend_step hFuel (by
    calc
      g0Final.toNat ≤ data.g0.toNat + 96 +
          orderArrayBytes (data.orders.length - 1) +
          tradeArrayBytes (data.tradeValues.length + 1) := hHeapUpper
      _ ≤ data.g0.toNat + Budget.stepBytes ctx.bookLimit ctx.tradeLimit := by
        simpa [Nat.add_assoc] using Nat.add_le_add_left
          (Budget.fullStepBytes_le facts.bookLength hTradeLimit) data.g0.toNat)
    facts.budget
  refine {
    locals := ?_
    bookOwner := by simp [nextData]
    oldTradesTracker := by simp [nextData]
    fuelSpent := ?_
    source := ?_
    fullFills := ?_
    bookLength := ?_
    tradeLength := ?_
    book48 := hBook48
    book32 := hBook32
    bookCapacity := hBookCapacity
    bookBelow := hBookBelow
    bookFree := hBookFree
    trades48 := hTrades48
    trades32 := hTrades32
    tradesCapacity := hTradesCapacity
    tradesBelow := hTradesBelow
    tradesFree := hTradesFree
    nodesBelow := hNodesBelow
    bookOwned := hBookOwned
    tradesOwned := hTradesOwned
    freeList := hFreeList
    global0 := hG0
    global1 := hG1
    global2 := hG2
    global4 := hG4
    global5 := hG5
    allocationCounter := ?_
    releaseCounter4 := ?_
    releaseCounter5 := ?_
    pages := ?_
    pageLimit := ?_
    addressLimit := facts.addressLimit
    memoryLimit := ?_
    budget := hBudget }
  · rcases hRecursive with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
      hTrader, hSide, hPrice, hQtyLocal, hBookOwner, hBook, hTrades,
      hRemainingLocal, hOldBook, hOldTrades, hDone⟩
    exact ⟨hParams, hLocals, hValues, hFuelLocal, hOid, hTrader, hSide,
      hPrice, hQtyLocal, hBookOwner, hBook, hTrades, hRemainingLocal,
      hOldBook, hOldTrades, hDone, hScratch⟩
  · simp only [nextData]
    calc
      ctx.initialFuel.toNat = data.steps + data.fuel.toNat := facts.fuelSpent
      _ = data.steps + 1 + (data.fuel - 1).toNat := by
        rw [Budget.fuel_sub_one_toNat data.fuel hFuel]
        have hFuelPositive : 0 < data.fuel.toNat := by
          by_contra h
          have hZero : data.fuel.toNat = 0 := by omega
          apply hFuel
          apply UInt64.toNat.inj
          simpa using hZero
        omega
  · simpa [nextData, fullState, RunningData.sourceState] using hSource
  · simpa [nextData, fullState, RunningData.sourceState] using hFills
  · simp only [nextData]
    rw [List.length_eraseIdx_of_lt hi]
    exact (Nat.pred_le _).trans facts.bookLength
  · simp only [nextData, List.length_append, List.length_singleton]
    rw [facts.tradeLength]
    omega
  · simp only [nextData]
    rw [facts.allocationCounter]
    exact allocationCounter_next ctx.initialG2 data.steps
  · simp only [nextData]
    rw [facts.releaseCounter4, hRelease]
    exact releaseCounter_next ctx.initialG4 data.steps
  · simp only [nextData]
    rw [facts.releaseCounter5, hRelease]
    exact releaseCounter_next ctx.initialG5 data.steps
  · rw [hPages, facts.pages]
  · rw [hPages]
    exact facts.pageLimit
  · rw [hPages]
    exact facts.memoryLimit

end Project.ClobMatchFuel.LoopAdvance
