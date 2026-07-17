import Project.ClobLimit.InternalLoopCompletion
import Project.ClobLimit.InternalFullBranch

/-!
# Internal match-loop full-fill advancement

A full fill replaces both arrays, decrements fuel, and advances the allocation
counter by two.  This module combines the physical branch result with source
progress, heap preservation, and the fixed step budget.  The result establishes
the complete running invariant for the next iteration.
-/

namespace Project.ClobLimit.InternalLoopAdvance

open Wasm Project.Clob Project.ClobFindBest.Model Project.ClobLimit
  Project.ClobLimit.InternalFullBranch
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobLimit.InternalLoopProgress
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def nextData (data : RunningData) (taker : OrderL) (i : Nat)
    (newBook newBookCapacity newTrades newTradesCapacity g0Final : UInt64) :
    RunningData :=
  { steps := data.steps + 1
    fuel := data.fuel - 1
    bookOwner := newBook
    book := newBook
    bookCapacity := newBookCapacity
    tradesOwner := newTrades
    trades := newTrades
    tradesCapacity := newTradesCapacity
    remaining := data.remaining - data.orders[i]!.oqty
    g0 := g0Final
    g2 := data.g2 + 2
    orders := data.orders.eraseIdx i
    tradeValues := data.tradeValues ++
      [Project.ClobMatchFuel.Model.fillTradeL taker data.orders[i]!
        data.orders[i]!.oqty] }

theorem of_full (ctx : Context) (st : Store Unit) (s : Locals)
    (data : RunningData) (facts : RunningFacts ctx st s data)
    (hFuel : data.fuel ≠ 0) (i : Nat) (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : data.orders[i]!.oqty ≤ data.remaining)
    (st1 : Store Unit) (s1 : Locals)
    (newBook newBookCapacity newTrades newTradesCapacity g0Final : UInt64)
    (hRecursive : RecursiveResultAt s1 data.fuel ctx.taker newBook newTrades
      (data.remaining - data.orders[i]!.oqty))
    (hBookOwned : OwnedOrderArrayAt st1 newBook newBookCapacity
      (data.orders.eraseIdx i))
    (hTradesOwned : OwnedTradeArrayAt st1 newTrades newTradesCapacity
      (data.tradeValues ++
        [Project.ClobMatchFuel.Model.fillTradeL ctx.taker data.orders[i]!
          data.orders[i]!.oqty]))
    (hBook48 : 48 ≤ newBook.toNat)
    (hBook32 : newBook.toNat +
      fixedArrayBytes (data.orders.eraseIdx i).length 5 < 4294967296)
    (hBookCapacity :
      fixedArrayBytes (data.orders.eraseIdx i).length 5 ≤
        newBookCapacity.toNat)
    (hBookBelow : newBook.toNat + newBookCapacity.toNat ≤ g0Final.toNat)
    (hTrades48 : 48 ≤ newTrades.toNat)
    (hTrades32 : newTrades.toNat + fixedArrayBytes
      (data.tradeValues ++
        [Project.ClobMatchFuel.Model.fillTradeL ctx.taker data.orders[i]!
          data.orders[i]!.oqty]).length 4 < 4294967296)
    (hTradesCapacity : fixedArrayBytes
      (data.tradeValues ++
        [Project.ClobMatchFuel.Model.fillTradeL ctx.taker data.orders[i]!
          data.orders[i]!.oqty]).length 4 ≤ newTradesCapacity.toNat)
    (hTradesBelow : newTrades.toNat + newTradesCapacity.toNat ≤
      g0Final.toNat)
    (hHeapLower : data.g0.toNat ≤ g0Final.toNat)
    (hHeapUpper : g0Final.toNat ≤ data.g0.toNat + 96 +
      orderArrayBytes (data.orders.length - 1) +
      tradeArrayBytes (data.tradeValues.length + 1))
    (hPages : st1.mem.pages = st.mem.pages)
    (hG0 : st1.globals.globals[0]? = some (.i64 g0Final))
    (hG1 : st1.globals.globals[1]? = some (.i64 0))
    (hG2 : st1.globals.globals[2]? = some (.i64 (data.g2 + 2)))
    (hBelow : ∀ a : Nat, a < data.g0.toNat →
      st1.mem.bytes a = st.mem.bytes a) :
    RunningFacts ctx st1 s1
      (nextData data ctx.taker i newBook newBookCapacity newTrades
        newTradesCapacity g0Final) := by
  have hi : i < data.orders.length :=
    findBestL_some_lt data.orders ctx.taker i hFind
  have hSource := full_source ctx st s data facts hFuel i hRemaining hFind hQty
  have hTradeLimit : data.tradeValues.length + 1 ≤ ctx.tradeLimit := by
    rw [facts.tradeLength]
    unfold Context.tradeLimit
    have hFuelSpent := facts.fuelSpent
    have hFuelPositive : 0 < data.fuel.toNat := by
      by_contra h
      have hZero : data.fuel.toNat = 0 := by omega
      apply hFuel
      apply UInt64.toNat.inj
      simpa using hZero
    omega
  have hBudget := Project.ClobMatchFuel.Budget.spend_step hFuel (by
    calc
      g0Final.toNat ≤ data.g0.toNat + 96 +
          orderArrayBytes (data.orders.length - 1) +
          tradeArrayBytes (data.tradeValues.length + 1) := hHeapUpper
      _ ≤ data.g0.toNat + Project.ClobMatchFuel.Budget.stepBytes
          ctx.bookLimit ctx.tradeLimit := by
        simpa [Nat.add_assoc] using Nat.add_le_add_left
          (Project.ClobMatchFuel.Budget.fullStepBytes_le facts.bookLength
            hTradeLimit) data.g0.toNat)
    facts.budget
  have hStepBelow : BytesEqBelow st.mem st1.mem ctx.initialG0.toNat := by
    intro a ha
    exact hBelow a (ha.trans_le facts.heapMono)
  refine {
    locals := ?_
    fuelSpent := ?_
    source := ?_
    bookLength := ?_
    tradeLength := ?_
    book48 := hBook48
    book32 := hBook32
    bookCapacity := hBookCapacity
    bookBelow := hBookBelow
    trades48 := hTrades48
    trades32 := hTrades32
    tradesCapacity := hTradesCapacity
    tradesBelow := hTradesBelow
    bookOwned := hBookOwned
    tradesOwned := hTradesOwned
    global0 := hG0
    global1 := hG1
    global2 := hG2
    allocationCounter := ?_
    heapMono := facts.heapMono.trans hHeapLower
    memoryBelow := facts.memoryBelow.trans hStepBelow
    pages := ?_
    pageLimit := ?_
    addressLimit := facts.addressLimit
    memoryLimit := ?_
    budget := hBudget }
  · rcases hRecursive with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
      hTrader, hSide, hPrice, hQtyLocal, hBookOwner, hBook, hTradesOwner,
      hTrades, hRemainingLocal, hRunning, hScratch⟩
    exact ⟨hParams, hLocals, hValues, hFuelLocal, hOid, hTrader, hSide,
      hPrice, hQtyLocal, hBookOwner, hBook, hTradesOwner, hTrades,
      hRemainingLocal, hRunning, hScratch⟩
  · simp only [nextData]
    calc
      ctx.initialFuel.toNat = data.steps + data.fuel.toNat := facts.fuelSpent
      _ = data.steps + 1 + (data.fuel - 1).toNat := by
        rw [Project.ClobMatchFuel.Budget.fuel_sub_one_toNat data.fuel hFuel]
        have hFuelPositive : 0 < data.fuel.toNat := by
          by_contra h
          have hZero : data.fuel.toNat = 0 := by omega
          apply hFuel
          apply UInt64.toNat.inj
          simpa using hZero
        omega
  · simpa [nextData, fullState, RunningData.sourceState] using hSource
  · simp only [nextData]
    rw [List.length_eraseIdx_of_lt hi]
    exact (Nat.pred_le _).trans facts.bookLength
  · simp only [nextData, List.length_append, List.length_singleton]
    rw [facts.tradeLength]
    omega
  · simp only [nextData]
    rw [facts.allocationCounter]
    exact allocationCounter_next ctx.initialG2 data.steps
  · rw [hPages, facts.pages]
  · rw [hPages]
    exact facts.pageLimit
  · rw [hPages]
    exact facts.memoryLimit

end Project.ClobLimit.InternalLoopAdvance
