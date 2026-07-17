import Project.ClobLimit.InternalLoopAdvance

/-!
# Internal match-loop branch composition

The dispatcher enters allocation branches through a selected-maker frame.  The
partial theorem returns a completed invariant, while the full theorem returns
the next running invariant.  Each continuation also proves a strict decrease
of the loop measure.
-/

namespace Project.ClobLimit.InternalLoopBranches

open Wasm Project.Clob Project.ClobFindBest.Model Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobLimit.InternalLoopBounds
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem partial_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (data : RunningData)
    (facts : RunningFacts ctx st base data)
    (bounds : StepBounds ctx st data) (hFuel : data.fuel ≠ 0) (i : Nat)
    (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : ¬data.orders[i]!.oqty ≤ data.remaining)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s1, CompletedAt ctx st1 s1 →
      measure st1 s1 < measure st base →
      wp «module» rest Q st1 s1 env) :
    wp «module» (InternalPartialBranch.partialBranchProg ++ rest) Q st
      (InternalIteration.quantityFrame base data.bookOwner data.book
        ctx.taker i) env := by
  rcases facts.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
    hTrader, hSide, hPrice, hQtyLocal, hBookOwner, hBook, hTradesOwner,
    hTrades, hRemainingLocal, hRunning, hScratch⟩
  rcases hScratch with
    ⟨bookCapacity, bookNext, tradeNext, partialNext, h58, h59, h61, h62⟩
  have hi : i < data.orders.length :=
    findBestL_some_lt data.orders ctx.taker i hFind
  apply InternalPartialBranch.partialBranchProg_spec env st
    (InternalIteration.quantityFrame base data.bookOwner data.book ctx.taker i)
    data.book data.bookCapacity data.trades data.tradesCapacity data.remaining
    data.fuel data.g0 data.g2 tradeNext partialNext ctx.taker data.orders
    data.tradeValues i
  · simpa [InternalIteration.quantityFrame] using hParams
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      List.length_set] using hLocals
  · simp [InternalIteration.quantityFrame]
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hFuelLocal
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hOid
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hBook
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hTrades
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hRemainingLocal
  · simp [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      optionPayload, hLocals]
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      hLocals] using h61
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      hLocals] using h62
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
  · exact bounds.partialTradeTopAfterBook
  · exact bounds.partialTradeFit32AfterBook
  · exact bounds.partialTradeFitAfterBook
  · exact facts.pageLimit
  · exact facts.book48
  · exact facts.book32
  · exact facts.bookCapacity
  · exact facts.bookBelow
  · exact facts.bookOwned
  · exact facts.trades48
  · exact facts.trades32
  · exact facts.tradesCapacity
  · exact facts.tradesBelow
  · exact facts.tradesOwned
  · exact facts.global0
  · exact facts.global1
  · exact facts.global2
  · intro st1 s1 hResult hBookOwned hNewBookOwned hTradesOwned hNewTradesOwned
      hPages hG0 hG1 hG2 hBelow
    have hBookNeed :
        (orderArrayBytesU data.orders.length).toNat =
          orderArrayBytes data.orders.length :=
      fixedArrayBytesU_toNat data.orders.length 5 bounds.ordersLength64
        (by decide) (by
          have hBytes := bounds.partialBookBytes
          change fixedArrayBytes data.orders.length 5 + 7 < UInt64.size at hBytes
          omega)
    have hTradeNeed :
        (tradeArrayBytesU (data.tradeValues.length + 1)).toNat =
          tradeArrayBytes (data.tradeValues.length + 1) :=
      fixedArrayBytesU_toNat (data.tradeValues.length + 1) 4
        bounds.tradeLength64 (by decide) (by
          have hBytes := bounds.tradeBytes
          change fixedArrayBytes (data.tradeValues.length + 1) 4 + 7 <
            UInt64.size at hBytes
          omega)
    have hHeapLimit :
        (data.g0 + 48 + orderArrayBytesU data.orders.length + 48 +
          tradeArrayBytesU (data.tradeValues.length + 1)).toNat ≤ ctx.limit := by
      rw [bounds.partialTradeTopAfterBook, bounds.partialBookTop, hBookNeed,
        hTradeNeed]
      have hLimit := bounds.partialAllocationLimit
      omega
    have hCompleted := InternalLoopCompletion.of_partial ctx st base data facts
      hFuel i hRemaining hFind hQty st1 s1 (data.g0 + 48)
      (orderArrayBytesU data.orders.length)
      (data.g0 + 48 + orderArrayBytesU data.orders.length + 48)
      (tradeArrayBytesU (data.tradeValues.length + 1))
      (data.g0 + 48 + orderArrayBytesU data.orders.length + 48 +
        tradeArrayBytesU (data.tradeValues.length + 1))
      hResult hNewBookOwned hNewTradesOwned hPages hG0 hG1 hG2 hHeapLimit
      hBelow
    apply hDone st1 s1 hCompleted
    rw [measure_completed hCompleted, measure_running facts]
    omega

set_option Elab.async false in
theorem full_spec (env : HostEnv Unit) (ctx : Context) (st : Store Unit)
    (base : Locals) (data : RunningData)
    (facts : RunningFacts ctx st base data)
    (bounds : StepBounds ctx st data) (hFuel : data.fuel ≠ 0) (i : Nat)
    (hRemaining : data.remaining ≠ 0)
    (hFind : findBestL data.orders ctx.taker = some i)
    (hQty : data.orders[i]!.oqty ≤ data.remaining)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s1, RunningAt ctx st1 s1 →
      measure st1 s1 < measure st base →
      wp «module» rest Q st1 s1 env) :
    wp «module» (InternalFullBranch.fullBranchProg ++ rest) Q st
      (InternalIteration.quantityFrame base data.bookOwner data.book
        ctx.taker i) env := by
  rcases facts.locals with ⟨hParams, hLocals, hValues, hFuelLocal, hOid,
    hTrader, hSide, hPrice, hQtyLocal, hBookOwner, hBook, hTradesOwner,
    hTrades, hRemainingLocal, hRunning, hScratch⟩
  rcases hScratch with
    ⟨bookCapacity, bookNext, tradeNext, partialNext, h58, h59, h61, h62⟩
  have hi : i < data.orders.length :=
    findBestL_some_lt data.orders ctx.taker i hFind
  apply InternalFullBranch.fullBranchProg_spec env st
    (InternalIteration.quantityFrame base data.bookOwner data.book ctx.taker i)
    data.book data.bookCapacity data.trades data.tradesCapacity data.fuel
    data.remaining data.g0 data.g2 bookCapacity bookNext tradeNext ctx.taker
    data.orders data.tradeValues i
  · simpa [InternalIteration.quantityFrame] using hParams
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      List.length_set] using hLocals
  · simp [InternalIteration.quantityFrame]
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hFuelLocal
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hRunning
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hOid
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hTrader
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hSide
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hPrice
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hQtyLocal
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hBook
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hTrades
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      Locals.get, hParams, hLocals] using hRemainingLocal
  · simp [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      optionPayload, Locals.get, hParams, hLocals]
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      hLocals] using h58
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      hLocals] using h59
  · simpa [InternalIteration.quantityFrame, InternalIteration.searchLocals,
      hLocals] using h61
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
  · exact bounds.fullTradeTopAfterBook
  · exact bounds.fullTradeFit32AfterBook
  · exact bounds.fullTradeFitAfterBook
  · exact facts.pageLimit
  · exact facts.book48
  · exact facts.book32
  · exact facts.bookCapacity
  · exact facts.bookBelow
  · exact facts.bookOwned
  · exact facts.trades48
  · exact facts.trades32
  · exact facts.tradesCapacity
  · exact facts.tradesBelow
  · exact facts.tradesOwned
  · exact facts.global0
  · exact facts.global1
  · exact facts.global2
  · intro st1 s1 hRecursive hBookOwned hNewBookOwned hTradesOwned
      hNewTradesOwned hPages hG0 hG1 hG2 hBelow
    have hBookNeedNat :
        (orderArrayBytesU (data.orders.length - 1)).toNat =
          orderArrayBytes (data.orders.length - 1) :=
      fixedArrayBytesU_toNat (data.orders.length - 1) 5
        bounds.erasedLength64 (by decide) (by
          have h := bounds.fullBookBytes
          unfold orderArrayBytes at h
          omega)
    have hTradeNeedNat :
        (tradeArrayBytesU (data.tradeValues.length + 1)).toNat =
          tradeArrayBytes (data.tradeValues.length + 1) :=
      fixedArrayBytesU_toNat (data.tradeValues.length + 1) 4
        bounds.tradeLength64 (by decide) (by
          have h := bounds.tradeBytes
          unfold tradeArrayBytes at h
          omega)
    have hNewBookNat : (data.g0 + 48).toNat = data.g0.toNat + 48 := by
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      have hFit32 := bounds.fullBookFit32
      rw [h48, Nat.mod_eq_of_lt]
      omega
    have hG0AfterBookNat :
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1)).toNat =
          data.g0.toNat + 48 +
            (orderArrayBytesU (data.orders.length - 1)).toNat :=
      bounds.fullBookTop
    have hNewTradesNat :
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48).toNat =
          (data.g0 + 48 +
            orderArrayBytesU (data.orders.length - 1)).toNat + 48 := by
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      have hFit32 := bounds.fullTradeFit32AfterBook
      rw [h48, Nat.mod_eq_of_lt]
      omega
    have hFinalNat :
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48 +
          tradeArrayBytesU (data.tradeValues.length + 1)).toNat =
        (data.g0 + 48 +
          orderArrayBytesU (data.orders.length - 1)).toNat + 48 +
          (tradeArrayBytesU (data.tradeValues.length + 1)).toNat :=
      bounds.fullTradeTopAfterBook
    have hNewBook48 : 48 ≤ (data.g0 + 48).toNat := by
      rw [hNewBookNat]
      omega
    have hNewBook32 : (data.g0 + 48).toNat +
        fixedArrayBytes (data.orders.eraseIdx i).length 5 < 4294967296 := by
      rw [List.length_eraseIdx_of_lt hi, hNewBookNat]
      change data.g0.toNat + 48 + orderArrayBytes (data.orders.length - 1) <
        4294967296
      rw [← hBookNeedNat]
      exact bounds.fullBookFit32
    have hNewBookCapacity :
        fixedArrayBytes (data.orders.eraseIdx i).length 5 ≤
          (orderArrayBytesU (data.orders.length - 1)).toNat := by
      rw [List.length_eraseIdx_of_lt hi, hBookNeedNat]
    have hNewBookBelow : (data.g0 + 48).toNat +
        (orderArrayBytesU (data.orders.length - 1)).toNat ≤
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48 +
          tradeArrayBytesU (data.tradeValues.length + 1)).toNat := by
      rw [hNewBookNat, hFinalNat, hG0AfterBookNat]
      omega
    have hNewTrades48 : 48 ≤
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48).toNat := by
      rw [hNewTradesNat]
      omega
    have hNewTrades32 :
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48).toNat +
          fixedArrayBytes
            (data.tradeValues ++
              [Project.ClobMatchFuel.Model.fillTradeL ctx.taker
                data.orders[i]! data.orders[i]!.oqty]).length 4 <
            4294967296 := by
      rw [List.length_append, List.length_singleton, hNewTradesNat]
      change (data.g0 + 48 +
          orderArrayBytesU (data.orders.length - 1)).toNat + 48 +
        tradeArrayBytes (data.tradeValues.length + 1) < 4294967296
      rw [← hTradeNeedNat]
      exact bounds.fullTradeFit32AfterBook
    have hNewTradesCapacity : fixedArrayBytes
        (data.tradeValues ++
          [Project.ClobMatchFuel.Model.fillTradeL ctx.taker data.orders[i]!
            data.orders[i]!.oqty]).length 4 ≤
        (tradeArrayBytesU (data.tradeValues.length + 1)).toNat := by
      rw [List.length_append, List.length_singleton, hTradeNeedNat]
    have hNewTradesBelow :
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48).toNat +
          (tradeArrayBytesU (data.tradeValues.length + 1)).toNat ≤
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48 +
          tradeArrayBytesU (data.tradeValues.length + 1)).toNat := by
      rw [hNewTradesNat, hFinalNat]
    have hHeapLower : data.g0.toNat ≤
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48 +
          tradeArrayBytesU (data.tradeValues.length + 1)).toNat := by
      rw [hFinalNat, hG0AfterBookNat]
      omega
    have hHeapUpper :
        (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48 +
          tradeArrayBytesU (data.tradeValues.length + 1)).toNat ≤
        data.g0.toNat + 96 + orderArrayBytes (data.orders.length - 1) +
          tradeArrayBytes (data.tradeValues.length + 1) := by
      rw [hFinalNat, hG0AfterBookNat, hBookNeedNat, hTradeNeedNat]
      omega
    have hNext := InternalLoopAdvance.of_full ctx st base data facts hFuel i
      hRemaining hFind hQty st1 s1 (data.g0 + 48)
      (orderArrayBytesU (data.orders.length - 1))
      (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48)
      (tradeArrayBytesU (data.tradeValues.length + 1))
      (data.g0 + 48 + orderArrayBytesU (data.orders.length - 1) + 48 +
        tradeArrayBytesU (data.tradeValues.length + 1))
      hRecursive hNewBookOwned hNewTradesOwned hNewBook48 hNewBook32
      hNewBookCapacity hNewBookBelow hNewTrades48 hNewTrades32
      hNewTradesCapacity hNewTradesBelow hHeapLower hHeapUpper hPages hG0 hG1
      hG2 hBelow
    have hRunningNext : RunningAt ctx st1 s1 := ⟨_, hNext⟩
    apply hDone st1 s1 hRunningNext
    rw [measure_running hNext, measure_running facts]
    change 2 * (data.fuel - 1).toNat + 1 < 2 * data.fuel.toNat + 1
    rw [Project.ClobMatchFuel.Budget.fuel_sub_one_toNat data.fuel hFuel]
    have hFuelPositive : 0 < data.fuel.toNat := by
      by_contra h
      have hZero : data.fuel.toNat = 0 := by omega
      apply hFuel
      apply UInt64.toNat.inj
      simpa using hZero
    omega

end Project.ClobLimit.InternalLoopBranches
