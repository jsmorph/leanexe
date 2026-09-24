import Project.ClobMatchFuel.LoopProgress

/-!
# Match-loop completion facts

A stopped iteration returns the current owned arrays.  A partial fill returns
the two replacement arrays after one appended trade.  These constructors turn
both physical outcomes into the completed loop invariant.
-/

namespace Project.ClobMatchFuel.LoopCompletion

open Wasm Project.Clob Project.Runtime Project.ClobFindBest.Model
  Project.ClobMatchFuel Project.ClobMatchFuel.LoopInvariant
  Project.ClobMatchFuel.LoopProgress
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def stoppedData (data : RunningData) : CompletedData :=
  { book := data.book, bookCapacity := data.bookCapacity,
    trades := data.trades, tradesCapacity := data.tradesCapacity,
    fuel := data.fuel, g0 := data.g0, nodes := data.nodes }

def partialData (fuel newBook newBookCapacity newTrades newTradesCapacity g0Final : UInt64)
    (nodes : List FreeNode) : CompletedData :=
  { book := newBook, bookCapacity := newBookCapacity,
    trades := newTrades, tradesCapacity := newTradesCapacity,
    fuel := fuel, g0 := g0Final, nodes := nodes }

theorem of_stop (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0)
    (hStop : data.remaining = 0 ∨ findBestL data.orders ctx.taker = none)
    (s1 : Locals)
    (hResult : LoopControl.CompletedResultAt s1 data.book data.trades
      data.remaining)
    (hFuelResult : s1.get 0 = some (.i64 data.fuel)) :
    CompletedFacts ctx st s1 (stoppedData data) := by
  obtain ⟨hSource, hFills⟩ := stopped_source ctx st s data facts hFuel hStop
  have hG2 := expectedG2_current ctx st s data facts (by
    rw [hSource]
    rfl)
  have hG4 := expectedG4_current ctx st s data facts hFills
  have hG5 := expectedG5_current ctx st s data facts hFills
  refine {
    result := ?_
    fuelLocal := hFuelResult
    book48 := facts.book48
    book32 := by simpa [stoppedData, hSource, RunningData.sourceState] using facts.book32
    bookCapacity := by simpa [stoppedData, hSource, RunningData.sourceState] using facts.bookCapacity
    bookBelow := facts.bookBelow
    bookFree := facts.bookFree
    trades48 := facts.trades48
    trades32 := by simpa [stoppedData, hSource, RunningData.sourceState] using facts.trades32
    tradesCapacity := by simpa [stoppedData, hSource, RunningData.sourceState] using facts.tradesCapacity
    tradesBelow := facts.tradesBelow
    tradesFree := facts.tradesFree
    nodesBelow := facts.nodesBelow
    heapLimit := by have h := facts.budget; dsimp [stoppedData]; omega
    pageLimit := facts.pageLimit
    addressLimit := facts.addressLimit
    memoryLimit := facts.memoryLimit
    bookOwned := ?_
    tradesOwned := ?_
    freeList := facts.freeList
    memoryFrame := facts.memoryFrame
    pages := facts.pages
    global0 := facts.global0
    global1 := facts.global1
    global2 := ?_
    global4 := ?_
    global5 := ?_ }
  · simpa [stoppedData, hSource, RunningData.sourceState] using hResult
  · simpa [stoppedData, hSource, RunningData.sourceState] using facts.bookOwned
  · simpa [stoppedData, hSource, RunningData.sourceState] using facts.tradesOwned
  · rw [← hG2]
    exact facts.global2
  · rw [← hG4]
    exact facts.global4
  · rw [← hG5]
    exact facts.global5

theorem of_partial (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : ¬data.orders[i]!.oqty ≤ data.remaining)
    (st1 : Store Unit) (s1 : Locals)
    (newBook newBookCapacity newTrades newTradesCapacity g0Final : UInt64)
    (nodes1 : List FreeNode)
    (hResult : PartialTradeUpdate.PartialResultAt s1 newBook newTrades data.fuel)
    (hBookOwned : OwnedOrderArrayAt st1 newBook newBookCapacity
      (Model.setQtyL data.orders i
        (data.orders[i]!.oqty - data.remaining)))
    (hTradesOwned : OwnedTradeArrayAt st1 newTrades newTradesCapacity
      (data.tradeValues ++
        [Model.fillTradeL ctx.taker data.orders[i]! data.remaining]))
    (hFreeList : FreeListAt st1.mem nodes1)
    (hMemoryFrame : MemoryFrame.BytesEqFrom ctx.initialMem st1.mem ctx.limit)
    (hPages : st1.mem.pages = st.mem.pages)
    (hG0 : st1.globals.globals[0]? = some (.i64 g0Final))
    (hG1 : st1.globals.globals[1]? = some (.i64 (freeHead nodes1)))
    (hG2 : st1.globals.globals[2]? = some (.i64 (data.g2 + 2)))
    (hG4 : st1.globals.globals[4]? = some (.i64 data.g4))
    (hG5 : st1.globals.globals[5]? = some (.i64 data.g5))
    (hBook48 : 48 ≤ newBook.toNat)
    (hBook32 : newBook.toNat + fixedArrayBytes (Model.setQtyL data.orders i
      (data.orders[i]!.oqty - data.remaining)).length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes (Model.setQtyL data.orders i
      (data.orders[i]!.oqty - data.remaining)).length 5 ≤ newBookCapacity.toNat)
    (hBookBelow : newBook.toNat + newBookCapacity.toNat ≤ g0Final.toNat)
    (hBookFree : FreeListSeparatedFromFixedArray nodes1 newBook newBookCapacity)
    (hTrades48 : 48 ≤ newTrades.toNat)
    (hTrades32 : newTrades.toNat + fixedArrayBytes (data.tradeValues.length + 1) 4 < 4294967296)
    (hTradesCapacity : fixedArrayBytes (data.tradeValues.length + 1) 4 ≤ newTradesCapacity.toNat)
    (hTradesBelow : newTrades.toNat + newTradesCapacity.toNat ≤ g0Final.toNat)
    (hTradesFree : FreeListSeparatedFromFixedArray nodes1 newTrades newTradesCapacity)
    (hNodesBelow : ∀ node ∈ nodes1, node.root.toNat + node.capacity.toNat ≤ g0Final.toNat)
    (hHeapLimit : g0Final.toNat ≤ ctx.limit) :
    CompletedFacts ctx st1 s1
      (partialData data.fuel newBook newBookCapacity newTrades newTradesCapacity g0Final nodes1) := by
  obtain ⟨hSource, hFills⟩ := partial_source ctx st s data facts hFuel i
    hRemaining hFind hQty
  have hResultTrades :
      ctx.result.trades.length = data.tradeValues.length + 1 := by
    rw [hSource]
    simp [partialState]
  have hExpectedG2 := expectedG2_after_append ctx st s data facts hResultTrades
  have hExpectedG4 := expectedG4_current ctx st s data facts hFills
  have hExpectedG5 := expectedG5_current ctx st s data facts hFills
  rcases hResult with ⟨hResultBook, hResultTradesRoot, hResultRemaining,
    hResultDone, hResultParams, hResultLocals, hResultValues, hResultFuel, _, _⟩
  have hCompletedResult :
      LoopControl.CompletedResultAt s1 newBook newTrades 0 :=
    ⟨hResultBook, hResultTradesRoot, hResultRemaining, hResultDone,
      hResultParams, hResultLocals, hResultValues⟩
  refine {
    result := ?_
    fuelLocal := hResultFuel
    book48 := hBook48
    book32 := by simpa [partialData, hSource, partialState] using hBook32
    bookCapacity := by simpa [partialData, hSource, partialState] using hBookCapacity
    bookBelow := hBookBelow
    bookFree := hBookFree
    trades48 := hTrades48
    trades32 := by simpa [partialData, hResultTrades] using hTrades32
    tradesCapacity := by simpa [partialData, hResultTrades] using hTradesCapacity
    tradesBelow := hTradesBelow
    tradesFree := hTradesFree
    nodesBelow := hNodesBelow
    heapLimit := hHeapLimit
    pageLimit := by rw [hPages]; exact facts.pageLimit
    addressLimit := facts.addressLimit
    memoryLimit := by rw [hPages]; exact facts.memoryLimit
    bookOwned := ?_
    tradesOwned := ?_
    freeList := hFreeList
    memoryFrame := hMemoryFrame
    pages := hPages.trans facts.pages
    global0 := hG0
    global1 := hG1
    global2 := ?_
    global4 := ?_
    global5 := ?_ }
  · simpa [partialData, LoopControl.CompletedResultAt, hSource, partialState] using
      hCompletedResult
  · simpa [partialData, hSource, partialState] using hBookOwned
  · simpa [partialData, hSource, partialState] using hTradesOwned
  · rw [← hExpectedG2]
    exact hG2
  · rw [← hExpectedG4]
    exact hG4
  · rw [← hExpectedG5]
    exact hG5

end Project.ClobMatchFuel.LoopCompletion
