import Project.ClobLimit.InternalLoopProgress

/-!
# Internal match-loop completion facts

A stopped iteration returns the current owned arrays and allocator state.  A
partial fill returns both replacement arrays after one appended trade.  These
constructors establish the completed loop invariant from either physical
outcome.
-/

namespace Project.ClobLimit.InternalLoopCompletion

open Wasm Project.Clob Project.ClobFindBest.Model Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobLimit.InternalLoopProgress
  Project.ClobLimit.InternalPartialTradeBranch
  Project.ClobMatchFuel.AllocatorFrame

theorem of_stop (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0)
    (hStop : data.remaining = 0 ∨ findBestL data.orders ctx.taker = none)
    (s1 : Locals)
    (hResult : InternalIteration.CompletedResultAt s1 data.bookOwner data.book
      data.tradesOwner data.trades data.remaining)
    (hFuelResult : s1.get 0 = some (.i64 data.fuel)) :
    CompletedAt ctx st s1 := by
  have hSource := stopped_source ctx st s data facts hFuel hStop
  have hExpectedG2 := expectedG2_current ctx st s data facts (by
    rw [hSource]
    rfl)
  refine ⟨{
    bookOwner := data.bookOwner
    book := data.book
    bookCapacity := data.bookCapacity
    tradesOwner := data.tradesOwner
    trades := data.trades
    tradesCapacity := data.tradesCapacity
    fuel := data.fuel
    g0 := data.g0 }, ?_⟩
  refine {
    result := ?_
    fuelLocal := hFuelResult
    bookOwned := ?_
    tradesOwned := ?_
    memoryBelow := facts.memoryBelow
    pages := facts.pages
    global0 := facts.global0
    global1 := facts.global1
    global2 := ?_ }
  · simpa [hSource, RunningData.sourceState] using hResult
  · simpa [hSource, RunningData.sourceState] using facts.bookOwned
  · simpa [hSource, RunningData.sourceState] using facts.tradesOwned
  · rw [← hExpectedG2]
    exact facts.global2

theorem of_partial (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : ¬data.orders[i]!.oqty ≤ data.remaining)
    (st1 : Store Unit) (s1 : Locals)
    (newBook newBookCapacity newTrades newTradesCapacity g0Final : UInt64)
    (hResult : PartialResultAt s1 newBook newTrades data.fuel)
    (hBookOwned : OwnedOrderArrayAt st1 newBook newBookCapacity
      (Project.ClobMatchFuel.Model.setQtyL data.orders i
        (data.orders[i]!.oqty - data.remaining)))
    (hTradesOwned : OwnedTradeArrayAt st1 newTrades newTradesCapacity
      (data.tradeValues ++
        [Project.ClobMatchFuel.Model.fillTradeL ctx.taker data.orders[i]!
          data.remaining]))
    (hPages : st1.mem.pages = st.mem.pages)
    (hG0 : st1.globals.globals[0]? = some (.i64 g0Final))
    (hG1 : st1.globals.globals[1]? = some (.i64 0))
    (hG2 : st1.globals.globals[2]? = some (.i64 (data.g2 + 2)))
    (hBelow : ∀ a : Nat, a < data.g0.toNat →
      st1.mem.bytes a = st.mem.bytes a) :
    CompletedAt ctx st1 s1 := by
  have hSource := partial_source ctx st s data facts hFuel i hRemaining hFind
    hQty
  have hResultTrades :
      ctx.result.trades.length = data.tradeValues.length + 1 := by
    rw [hSource]
    simp [partialState]
  have hExpectedG2 := expectedG2_after_append ctx st s data facts
    hResultTrades
  rcases hResult with ⟨hResultBookOwner, hResultBook, hResultTradesOwner,
    hResultTradesRoot, hResultRemaining, hResultDone, hResultParams,
    hResultLocals, hResultValues, hResultFuel⟩
  have hCompletedResult : InternalIteration.CompletedResultAt s1 newBook
      newBook newTrades newTrades 0 :=
    ⟨hResultBookOwner, hResultBook, hResultTradesOwner, hResultTradesRoot,
      hResultRemaining, hResultDone, hResultParams, hResultLocals,
      hResultValues⟩
  have hStepBelow : BytesEqBelow st.mem st1.mem ctx.initialG0.toNat := by
    intro a ha
    exact hBelow a (ha.trans_le facts.heapMono)
  refine ⟨{
    bookOwner := newBook
    book := newBook
    bookCapacity := newBookCapacity
    tradesOwner := newTrades
    trades := newTrades
    tradesCapacity := newTradesCapacity
    fuel := data.fuel
    g0 := g0Final }, ?_⟩
  refine {
    result := ?_
    fuelLocal := hResultFuel
    bookOwned := ?_
    tradesOwned := ?_
    memoryBelow := facts.memoryBelow.trans hStepBelow
    pages := hPages.trans facts.pages
    global0 := hG0
    global1 := hG1
    global2 := ?_ }
  · simpa [InternalIteration.CompletedResultAt, hSource, partialState] using
      hCompletedResult
  · simpa [hSource, partialState] using hBookOwned
  · simpa [hSource, partialState] using hTradesOwned
  · rw [← hExpectedG2]
    exact hG2

end Project.ClobLimit.InternalLoopCompletion
