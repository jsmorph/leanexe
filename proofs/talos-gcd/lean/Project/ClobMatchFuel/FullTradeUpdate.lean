import Project.ClobMatchFuel.FullBookUpdate
import Project.ClobMatchFuel.FullTradeFinish

/-!
# Full-fill trade update

The full-fill trade phase prepares the maker trade, allocates and appends it,
then computes the next remaining quantity.  This module preserves both books
needed across the trade writes and records the release-and-transition locals in
one postcondition.
-/

namespace Project.ClobMatchFuel.FullTradeUpdate

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def fullTradeUpdateProg : Wasm.Program :=
  FullTradePrepare.fullTradePrepareProg ++
    TradeAllocAppend.tradeAllocAppendProg ++
    FullTradeFinish.fullTradeFinishProg

def FullResultAt (s : Locals) (fuel : UInt64) (taker : OrderL)
    (oldBookTracker oldTradesTracker newBook newTrades remaining : UInt64) :
    Prop :=
  s.params.length = 9 ∧ s.locals.length = 76 ∧ s.values = [] ∧
  s.get 0 = some (.i64 fuel) ∧
  s.get 19 = some (.i64 oldBookTracker) ∧
  s.get 20 = some (.i64 oldTradesTracker) ∧
  s.get 34 = some (.i64 taker.oid) ∧
  s.get 35 = some (.i64 taker.otrader) ∧
  s.get 36 = some (.i64 taker.oside) ∧
  s.get 37 = some (.i64 taker.oprice) ∧
  s.get 38 = some (.i64 taker.oqty) ∧
  s.get 44 = some (.i64 newBook) ∧
  s.get 45 = some (.i64 newBook) ∧
  s.get 46 = some (.i64 newTrades) ∧
  s.get 47 = some (.i64 newTrades) ∧
  s.get 48 = some (.i64 remaining)

set_option Elab.async false in
theorem fullTradeUpdateProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel newBook newBookCapacity oldBook oldBookCapacity : UInt64)
    (oldTrades oldTradesCapacity remaining g0 g2 capacity next : UInt64)
    (oldBookTracker oldTradesTracker : UInt64)
    (taker : OrderL) (os newOrders : List OrderL)
    (ts : List TradeL) (i : Nat) (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [.i64 newBook])
    (hTakerLocal : base.locals[0]? = some (.i64 taker.oid))
    (hBookLocal : base.locals[6]? = some (.i64 oldBook))
    (hTradesLocal : base.locals[8]? = some (.i64 oldTrades))
    (hRemainingLocal : base.locals[9]? = some (.i64 remaining))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hCapacityLocal : base.locals[72]? = some (.i64 capacity))
    (hNextLocal : base.locals[73]? = some (.i64 next))
    (hFuel : base.get 0 = some (.i64 fuel))
    (hOldBookTracker : base.get 19 = some (.i64 oldBookTracker))
    (hOldTradesTracker : base.get 20 = some (.i64 oldTradesTracker))
    (hCarryOid : base.get 34 = some (.i64 taker.oid))
    (hCarryTrader : base.get 35 = some (.i64 taker.otrader))
    (hCarrySide : base.get 36 = some (.i64 taker.oside))
    (hCarryPrice : base.get 37 = some (.i64 taker.oprice))
    (hCarryQty : base.get 38 = some (.i64 taker.oqty))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hn : ts.length + 1 < UInt64.size)
    (hbytes : tradeArrayBytes (ts.length + 1) + 7 < UInt64.size)
    (hTotalU : (UInt64.ofNat ts.length * 4).toNat = ts.length * 4)
    (hTotal64 : ts.length * 4 < UInt64.size)
    (htop : (g0 + 48 + tradeArrayBytesU (ts.length + 1)).toNat =
      g0.toNat + 48 + (tradeArrayBytesU (ts.length + 1)).toNat)
    (hFit32 : g0.toNat + 48 +
      (tradeArrayBytesU (ts.length + 1)).toNat < 4294967296)
    (hFit : g0.toNat + 48 +
      (tradeArrayBytesU (ts.length + 1)).toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hOldTrades48 : 48 ≤ oldTrades.toNat)
    (hOldTrades32 :
      oldTrades.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hOldTradesCapacity :
      fixedArrayBytes ts.length 4 ≤ oldTradesCapacity.toNat)
    (hOldTradesBelow :
      oldTrades.toNat + oldTradesCapacity.toNat ≤ g0.toNat)
    (hOldTradesFree :
      FreeListSeparatedFromFixedArray nodes oldTrades oldTradesCapacity)
    (hNewBook48 : 48 ≤ newBook.toNat)
    (hNewBook32 :
      newBook.toNat + fixedArrayBytes newOrders.length 5 < 4294967296)
    (hNewBookCapacity :
      fixedArrayBytes newOrders.length 5 ≤ newBookCapacity.toNat)
    (hNewBookBelow :
      newBook.toNat + newBookCapacity.toNat ≤ g0.toNat)
    (hNewBookFree :
      FreeListSeparatedFromFixedArray nodes newBook newBookCapacity)
    (hOldBook48 : 48 ≤ oldBook.toNat)
    (hOldBook32 : oldBook.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hOldBookCapacity : fixedArrayBytes os.length 5 ≤ oldBookCapacity.toNat)
    (hOldBookBelow : oldBook.toNat + oldBookCapacity.toNat ≤ g0.toNat)
    (hOldBookFree :
      FreeListSeparatedFromFixedArray nodes oldBook oldBookCapacity)
    (hNodesBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat)
    (hOldTradesOwned :
      OwnedTradeArrayAt st oldTrades oldTradesCapacity ts)
    (hNewBookOwned :
      OwnedOrderArrayAt st newBook newBookCapacity newOrders)
    (hOldBookOwned : OwnedOrderArrayAt st oldBook oldBookCapacity os)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s newTrades newTradesCapacity nodes1 g0Final,
      FullResultAt s fuel taker oldBookTracker oldTradesTracker newBook
        newTrades (remaining - os[i]!.oqty) →
      OwnedOrderArrayAt st1 newBook newBookCapacity newOrders →
      OwnedTradeArrayAt st1 newTrades newTradesCapacity
        (ts ++ [Model.fillTradeL taker os[i]! os[i]!.oqty]) →
      OwnedOrderArrayAt st1 oldBook oldBookCapacity os →
      FreeListAt st1.mem nodes1 →
      st1.globals.globals[0]? = some (.i64 g0Final) →
      st1.globals.globals[1]? = some (.i64 (freeHead nodes1)) →
      st1.globals.globals[2]? = some (.i64 (g2 + 1)) →
      wp «module» rest Q st1 s env) :
    wp «module» (fullTradeUpdateProg ++ rest) Q st base env := by
  let trade := Model.fillTradeL taker os[i]! os[i]!.oqty
  have hFuelAt : base.params[0]? = some (.i64 fuel) := by
    simpa [Locals.get, hParams] using hFuel
  have hOldBookTrackerAt : base.locals[10]? =
      some (.i64 oldBookTracker) := by
    simpa [Locals.get, hParams, hLocals] using hOldBookTracker
  have hOldTradesTrackerAt : base.locals[11]? =
      some (.i64 oldTradesTracker) := by
    simpa [Locals.get, hParams, hLocals] using hOldTradesTracker
  have hCarryOidAt : base.locals[25]? = some (.i64 taker.oid) := by
    simpa [Locals.get, hParams, hLocals] using hCarryOid
  have hCarryTraderAt : base.locals[26]? = some (.i64 taker.otrader) := by
    simpa [Locals.get, hParams, hLocals] using hCarryTrader
  have hCarrySideAt : base.locals[27]? = some (.i64 taker.oside) := by
    simpa [Locals.get, hParams, hLocals] using hCarrySide
  have hCarryPriceAt : base.locals[28]? = some (.i64 taker.oprice) := by
    simpa [Locals.get, hParams, hLocals] using hCarryPrice
  have hCarryQtyAt : base.locals[29]? = some (.i64 taker.oqty) := by
    simpa [Locals.get, hParams, hLocals] using hCarryQty
  have hFuelElem : base.params[0] = .i64 fuel :=
    (List.getElem?_eq_some_iff.mp hFuelAt).2
  have hOldBookTrackerElem : base.locals[10] = .i64 oldBookTracker :=
    (List.getElem?_eq_some_iff.mp hOldBookTrackerAt).2
  have hOldTradesTrackerElem : base.locals[11] = .i64 oldTradesTracker :=
    (List.getElem?_eq_some_iff.mp hOldTradesTrackerAt).2
  have hCarryOidElem : base.locals[25] = .i64 taker.oid :=
    (List.getElem?_eq_some_iff.mp hCarryOidAt).2
  have hCarryTraderElem : base.locals[26] = .i64 taker.otrader :=
    (List.getElem?_eq_some_iff.mp hCarryTraderAt).2
  have hCarrySideElem : base.locals[27] = .i64 taker.oside :=
    (List.getElem?_eq_some_iff.mp hCarrySideAt).2
  have hCarryPriceElem : base.locals[28] = .i64 taker.oprice :=
    (List.getElem?_eq_some_iff.mp hCarryPriceAt).2
  have hCarryQtyElem : base.locals[29] = .i64 taker.oqty :=
    (List.getElem?_eq_some_iff.mp hCarryQtyAt).2
  unfold fullTradeUpdateProg
  rw [List.append_assoc, List.append_assoc]
  apply FullTradePrepare.fullTradePrepareProg_spec env st base newBook oldBook
    oldTrades taker os ts i hParams hLocals hValues hTakerLocal hBookLocal
    hTradesLocal hIndexLocal hi hOrdersLength64 hOldBookOwned.2
    hOldTradesOwned.2 Q
    (TradeAllocAppend.tradeAllocAppendProg ++
      FullTradeFinish.fullTradeFinishProg ++ rest)
  apply TradeAllocAppend.tradeAllocAppendProg_spec env st
    (FullTradePrepare.fullTradePrepareFrame base newBook oldBook oldTrades
      taker os[i]! i ts)
    oldTrades oldTradesCapacity newBook newBookCapacity g0 g2 capacity next ts
    trade newOrders nodes
  · simpa [FullTradePrepare.fullTradePrepareFrame] using hParams
  · simpa [FullTradePrepare.fullTradePrepareFrame, List.length_set] using
      hLocals
  · simp [FullTradePrepare.fullTradePrepareFrame]
  · simp [FullTradePrepare.fullTradePrepareFrame, hLocals]
  · simp [FullTradePrepare.fullTradePrepareFrame, hLocals]
  · simp [FullTradePrepare.fullTradePrepareFrame, hLocals]
  · simp [FullTradePrepare.fullTradePrepareFrame, hLocals]
  · simp [FullTradePrepare.fullTradePrepareFrame, trade,
      Model.fillTradeL, hLocals]
  · simp [FullTradePrepare.fullTradePrepareFrame, trade,
      Model.fillTradeL, hLocals]
  · simp [FullTradePrepare.fullTradePrepareFrame, trade,
      Model.fillTradeL, hLocals]
  · simp [FullTradePrepare.fullTradePrepareFrame, trade,
      Model.fillTradeL, hLocals]
  · simpa [FullTradePrepare.fullTradePrepareFrame,
      List.getElem?_set, hLocals] using hCapacityLocal
  · simpa [FullTradePrepare.fullTradePrepareFrame,
      List.getElem?_set, hLocals] using hNextLocal
  · exact hn
  · exact hbytes
  · exact hTotalU
  · exact hTotal64
  · exact htop
  · exact hFit32
  · exact hFit
  · exact hPages
  · exact hOldTrades48
  · exact hOldTrades32
  · exact hOldTradesCapacity
  · exact hOldTradesBelow
  · exact hOldTradesFree
  · exact hNewBook48
  · exact hNewBook32
  · exact hNewBookCapacity
  · exact hNewBookBelow
  · exact hNewBookFree
  · exact hNodesBelow
  · exact hOldTradesOwned
  · exact hNewBookOwned
  · exact hg0
  · exact hg1
  · exact hg2
  · exact hList
  · intro choice hTake st1 hTarget48 hTarget32 hTargetFit hOldTradesAlloc
      hNewTradesOwned hNewBookOwned1 hOutside hFinalPages hFinalGlobals
      hFinalList hFinalG0 hFinalG1
    let finalStore := TradeAppendStore.appendTradeStore st1 choice.node.root
      ts.length trade
    have hChoiceMem := takeFirstFitFrom_some_mem hTake
    have hChoiceCapacity := takeFirstFitFrom_some_capacity hTake
    have hNeedNat : (tradeArrayBytesU (ts.length + 1)).toNat =
        tradeArrayBytes (ts.length + 1) :=
      fixedArrayBytesU_toNat (ts.length + 1) 4 hn (by decide) (by
        change fixedArrayBytes (ts.length + 1) 4 + 7 < UInt64.size at hbytes
        omega)
    rw [UInt64.le_iff_toNat_le, hNeedNat] at hChoiceCapacity
    have hOldBookAlloc : OwnedOrderArrayAt
        (TradeAllocFit.tradeAllocFitStore st choice) oldBook oldBookCapacity
          os :=
      ownedOrderArrayAt_fixedArrayAllocFitStore hList hTake hOldBook48
        hOldBook32 hOldBookCapacity hOldBookFree hOldBookOwned
    have hPayloadBookSep : regionsDisjoint
        (flatWordsRegion choice.node.root ((ts.length + 1) * 4))
        (fixedArrayRegion oldBook oldBookCapacity) := by
      have hSep := hOldBookFree choice.node hChoiceMem
      unfold regionsDisjoint fixedArrayRegion FreeNode.region at hSep
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      unfold tradeArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hOldBookFinal : OwnedOrderArrayAt finalStore oldBook oldBookCapacity
        os :=
      OwnedOrderArrayAt.frame_outsideFlatWords hOldBook48 hOldBook32
        hOldBookCapacity hFinalPages hPayloadBookSep hOutside hOldBookAlloc
    have hFinalG2 : finalStore.globals.globals[2]? =
        some (.i64 (g2 + 1)) := by
      have hAllocG2 :
          (TradeAllocFit.tradeAllocFitStore st choice).globals.globals[2]? =
            some (.i64 g2) := by
        by_cases hPrevious : choice.previous = 0
        · simp only [TradeAllocFit.tradeAllocFitStore,
            BookAllocFit.fixedArrayAllocFitStore, hPrevious, if_pos]
          simpa [List.getElem?_set] using hg2
        · simp [TradeAllocFit.tradeAllocFitStore,
            BookAllocFit.fixedArrayAllocFitStore, hPrevious, hg2]
      have hAllocLength :
          2 < (TradeAllocFit.tradeAllocFitStore st choice).globals.globals.length :=
        (List.getElem?_eq_some_iff.mp hAllocG2).1
      rw [hFinalGlobals]
      simp [hAllocLength]
    apply FullTradeFinish.fullTradeFinishProg_spec env finalStore
      (TradeAppendFinish.tradeResultFrame
        (TradeAllocAppend.fitFrame
          (FullTradePrepare.fullTradePrepareFrame base newBook oldBook
            oldTrades taker os[i]! i ts) ts.length choice)
        choice.node.root (ts.length * 4)) choice.node.root oldBook remaining
      os i
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.fitFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame] using hParams
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.fitFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame, List.length_set] using hLocals
    · simp [TradeAppendFinish.tradeResultFrame]
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.fitFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame, hLocals] using hRemainingLocal
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.fitFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame, hLocals] using hBookLocal
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.fitFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame, hLocals] using hIndexLocal
    · exact hi
    · exact hOrdersLength64
    · exact hOldBookFinal.2
    · apply hDone finalStore _ choice.node.root choice.node.capacity
        choice.remaining g0
      · simp [FullResultAt, FullTradeFinish.fullTradeFinishFrame,
          TradeAppendFinish.tradeResultFrame, TradeAppendCopy.tradeCopyFrame,
          TradeAllocAppend.fitFrame, TradeAllocSearch.tradeAllocSearchFrame,
          FullTradePrepare.fullTradePrepareFrame, Locals.get, hParams,
          hLocals, hFuelElem, hOldBookTrackerElem, hOldTradesTrackerElem,
          hCarryOidElem, hCarryTraderElem, hCarrySideElem, hCarryPriceElem,
          hCarryQtyElem]
      · exact hNewBookOwned1
      · simpa [finalStore, trade] using hNewTradesOwned
      · exact hOldBookFinal
      · exact hFinalList
      · exact hFinalG0
      · exact hFinalG1
      · exact hFinalG2
  · intro previous st1 hTarget48 hTarget32 hTargetFit hOldTradesAlloc
      hNewTradesOwned hNewBookOwned1 hOutside hFinalPages hFinalGlobals
      hFinalList hFinalG0 hFinalG1
    let target := g0 + 48
    let finalStore := TradeAppendStore.appendTradeStore st1 target ts.length
      trade
    have hOldBookAlloc : OwnedOrderArrayAt
        (TradeAllocBump.tradeAllocBumpStore st g0
          (tradeArrayBytesU (ts.length + 1))) oldBook oldBookCapacity os :=
      ownedOrderArrayAt_fixedArrayAllocBumpStore hFit32 hOldBook48
        hOldBook32 hOldBookCapacity hOldBookBelow hOldBookOwned
    have hTargetNat : target.toNat = g0.toNat + 48 := by
      unfold target
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48, Nat.mod_eq_of_lt (by omega)]
    have hPayloadBookSep : regionsDisjoint
        (flatWordsRegion target ((ts.length + 1) * 4))
        (fixedArrayRegion oldBook oldBookCapacity) := by
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      rw [hTargetNat]
      omega
    have hOldBookFinal : OwnedOrderArrayAt finalStore oldBook oldBookCapacity
        os :=
      OwnedOrderArrayAt.frame_outsideFlatWords hOldBook48 hOldBook32
        hOldBookCapacity hFinalPages hPayloadBookSep hOutside hOldBookAlloc
    have hFinalG2 : finalStore.globals.globals[2]? =
        some (.i64 (g2 + 1)) := by
      have hAllocG2 :
          (TradeAllocBump.tradeAllocBumpStore st g0
            (tradeArrayBytesU (ts.length + 1))).globals.globals[2]? =
              some (.i64 g2) := by
        simp [TradeAllocBump.tradeAllocBumpStore,
          BookAllocBump.fixedArrayAllocBumpStore, hg2]
      have hAllocLength : 2 <
          (TradeAllocBump.tradeAllocBumpStore st g0
            (tradeArrayBytesU (ts.length + 1))).globals.globals.length :=
        (List.getElem?_eq_some_iff.mp hAllocG2).1
      change
        (TradeAppendStore.appendTradeStore st1 (g0 + 48) ts.length
          trade).globals.globals[2]? = some (.i64 (g2 + 1))
      rw [hFinalGlobals]
      simp [hAllocLength]
    apply FullTradeFinish.fullTradeFinishProg_spec env finalStore
      (TradeAppendFinish.tradeResultFrame
        (TradeAllocAppend.bumpFrame
          (FullTradePrepare.fullTradePrepareFrame base newBook oldBook
            oldTrades taker os[i]! i ts) ts.length g0 previous)
        target (ts.length * 4)) target oldBook remaining os i
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.bumpFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame] using hParams
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.bumpFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame, List.length_set] using hLocals
    · simp [TradeAppendFinish.tradeResultFrame, target]
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.bumpFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame, hLocals] using hRemainingLocal
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.bumpFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame, hLocals] using hBookLocal
    · simpa [TradeAppendFinish.tradeResultFrame,
        TradeAppendCopy.tradeCopyFrame, TradeAllocAppend.bumpFrame,
        TradeAllocSearch.tradeAllocSearchFrame,
        FullTradePrepare.fullTradePrepareFrame, hLocals] using hIndexLocal
    · exact hi
    · exact hOrdersLength64
    · exact hOldBookFinal.2
    · apply hDone finalStore _ target
        (tradeArrayBytesU (ts.length + 1)) nodes
        (g0 + 48 + tradeArrayBytesU (ts.length + 1))
      · simp [FullResultAt, FullTradeFinish.fullTradeFinishFrame,
          TradeAppendFinish.tradeResultFrame, TradeAppendCopy.tradeCopyFrame,
          TradeAllocAppend.bumpFrame, TradeAllocSearch.tradeAllocSearchFrame,
          FullTradePrepare.fullTradePrepareFrame, Locals.get, hParams,
          hLocals, hFuelElem, hOldBookTrackerElem, hOldTradesTrackerElem,
          hCarryOidElem, hCarryTraderElem, hCarrySideElem, hCarryPriceElem,
          hCarryQtyElem, target]
      · exact hNewBookOwned1
      · simpa [finalStore, target, trade] using hNewTradesOwned
      · exact hOldBookFinal
      · exact hFinalList
      · exact hFinalG0
      · exact hFinalG1
      · exact hFinalG2

end Project.ClobMatchFuel.FullTradeUpdate
