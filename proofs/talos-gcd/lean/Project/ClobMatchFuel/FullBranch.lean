import Project.ClobMatchFuel.FullTradeUpdate

/-!
# Full-fill branch

The full-fill branch removes the matched maker, appends its trade, and records
the recursive result.  This module composes both allocators while retaining the
source arrays needed by the release block.
-/

namespace Project.ClobMatchFuel.FullBranch

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def fullBranchProg : Wasm.Program :=
  FullBookUpdate.fullBookUpdateProg ++ FullTradeUpdate.fullTradeUpdateProg

set_option Elab.async false in
theorem fullBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (fuel book bookCapacity oldTrades oldTradesCapacity remaining : UInt64)
    (g0 g2 capacity next tradeNext oldBookTracker oldTradesTracker : UInt64)
    (taker : OrderL) (os : List OrderL) (ts : List TradeL) (i : Nat)
    (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hTakerLocal : base.locals[0]? = some (.i64 taker.oid))
    (hBookLocal : base.locals[6]? = some (.i64 book))
    (hTradesLocal : base.locals[8]? = some (.i64 oldTrades))
    (hRemainingLocal : base.locals[9]? = some (.i64 remaining))
    (hIndexLocal : base.locals[24]? = some (.i64 (UInt64.ofNat i)))
    (hSourceLocal : base.locals[57]? = some (.i64 book))
    (hPrefixLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat (i * 5))))
    (hSuffixLocal : base.locals[61]? =
      some (.i64 (UInt64.ofNat ((os.length - 1 - i) * 5))))
    (hLengthLocal : base.locals[62]? =
      some (.i64 (UInt64.ofNat (os.length - 1))))
    (hCapacityLocal : base.locals[70]? = some (.i64 capacity))
    (hNextLocal : base.locals[71]? = some (.i64 next))
    (hTradeNextLocal : base.locals[73]? = some (.i64 tradeNext))
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
    (hErasedLength64 : os.length - 1 < UInt64.size)
    (hOrderWords64 : os.length * 5 < UInt64.size)
    (hBookBytes : orderArrayBytes (os.length - 1) + 7 < UInt64.size)
    (hBookTop : (g0 + 48 + orderArrayBytesU (os.length - 1)).toNat =
      g0.toNat + 48 + (orderArrayBytesU (os.length - 1)).toNat)
    (hBookFit32 : g0.toNat + 48 +
      (orderArrayBytesU (os.length - 1)).toNat < 4294967296)
    (hBookFit : g0.toNat + 48 +
      (orderArrayBytesU (os.length - 1)).toNat ≤ st.mem.pages * 65536)
    (hTradeLength64 : ts.length + 1 < UInt64.size)
    (hTradeBytes : tradeArrayBytes (ts.length + 1) + 7 < UInt64.size)
    (hTradeTotalU : (UInt64.ofNat ts.length * 4).toNat = ts.length * 4)
    (hTradeTotal64 : ts.length * 4 < UInt64.size)
    (hTradeTopAtG0 : (g0 + 48 + tradeArrayBytesU (ts.length + 1)).toNat =
      g0.toNat + 48 + (tradeArrayBytesU (ts.length + 1)).toNat)
    (hTradeFit32AtG0 : g0.toNat + 48 +
      (tradeArrayBytesU (ts.length + 1)).toNat < 4294967296)
    (hTradeFitAtG0 : g0.toNat + 48 +
      (tradeArrayBytesU (ts.length + 1)).toNat ≤ st.mem.pages * 65536)
    (hTradeTopAfterBook :
      (g0 + 48 + orderArrayBytesU (os.length - 1) + 48 +
          tradeArrayBytesU (ts.length + 1)).toNat =
        (g0 + 48 + orderArrayBytesU (os.length - 1)).toNat + 48 +
          (tradeArrayBytesU (ts.length + 1)).toNat)
    (hTradeFit32AfterBook :
      (g0 + 48 + orderArrayBytesU (os.length - 1)).toNat + 48 +
        (tradeArrayBytesU (ts.length + 1)).toNat < 4294967296)
    (hTradeFitAfterBook :
      (g0 + 48 + orderArrayBytesU (os.length - 1)).toNat + 48 +
          (tradeArrayBytesU (ts.length + 1)).toNat ≤
        st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hBook48 : 48 ≤ book.toNat)
    (hBook32 : book.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes os.length 5 ≤ bookCapacity.toNat)
    (hBookBelow : book.toNat + bookCapacity.toNat ≤ g0.toNat)
    (hBookFree : FreeListSeparatedFromFixedArray nodes book bookCapacity)
    (hOldTrades48 : 48 ≤ oldTrades.toNat)
    (hOldTrades32 :
      oldTrades.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hOldTradesCapacity :
      fixedArrayBytes ts.length 4 ≤ oldTradesCapacity.toNat)
    (hOldTradesBelow :
      oldTrades.toNat + oldTradesCapacity.toNat ≤ g0.toNat)
    (hOldTradesFree :
      FreeListSeparatedFromFixedArray nodes oldTrades oldTradesCapacity)
    (hNodesBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat)
    (hBookOwned : OwnedOrderArrayAt st book bookCapacity os)
    (hOldTradesOwned :
      OwnedTradeArrayAt st oldTrades oldTradesCapacity ts)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s newBook newBookCapacity newTrades
        newTradesCapacity nodes1 g0Final,
      FullTradeUpdate.FullResultAt s fuel taker oldBookTracker oldTradesTracker
        newBook newTrades (remaining - os[i]!.oqty) →
      OwnedOrderArrayAt st1 newBook newBookCapacity (os.eraseIdx i) →
      OwnedTradeArrayAt st1 newTrades newTradesCapacity
        (ts ++ [Model.fillTradeL taker os[i]! os[i]!.oqty]) →
      OwnedTradeArrayAt st1 oldTrades oldTradesCapacity ts →
      OwnedOrderArrayAt st1 book bookCapacity os →
      FreeListAt st1.mem nodes1 →
      st1.globals.globals[0]? = some (.i64 g0Final) →
      st1.globals.globals[1]? = some (.i64 (freeHead nodes1)) →
      st1.globals.globals[2]? = some (.i64 (g2 + 2)) →
      wp «module» rest Q st1 s env) :
    wp «module» (fullBranchProg ++ rest) Q st base env := by
  have hg2Next : g2 + 1 + 1 = g2 + 2 := by
    have h2 : (2 : UInt64) = 1 + 1 := by decide
    rw [h2]
    ac_rfl
  have hTradeNextElem : base.locals[73] = .i64 tradeNext :=
    (List.getElem?_eq_some_iff.mp hTradeNextLocal).2
  unfold fullBranchProg
  rw [List.append_assoc]
  apply FullBookUpdate.fullBookUpdateProg_spec env st base book bookCapacity
    oldTrades oldTradesCapacity g0 g2 capacity next os ts i nodes hParams
    hLocals hValues hSourceLocal hPrefixLocal hSuffixLocal hLengthLocal
    hCapacityLocal hNextLocal hi hErasedLength64 hOrderWords64 hBookBytes
    hBookTop hBookFit32 hBookFit hPages hBook48 hBook32 hBookCapacity
    hBookBelow hBookFree hOldTrades48 hOldTrades32 hOldTradesCapacity
    hOldTradesBelow hOldTradesFree hNodesBelow hBookOwned hOldTradesOwned hg0
    hg1 hg2 hList Q (FullTradeUpdate.fullTradeUpdateProg ++ rest)
  · intro choice hTake st1 hTarget48 hTarget32 hNewBookOwned hBookOwned1
      hOldTradesOwned1 hOutside hFinalPages hFinalGlobals hFinalList hFinalG0
      hFinalG1 hFinalG2
    have hChoiceMem : choice.node ∈ nodes := takeFirstFitFrom_some_mem hTake
    have hBookNeedNat : (orderArrayBytesU (os.length - 1)).toNat =
        orderArrayBytes (os.length - 1) :=
      fixedArrayBytesU_toNat (os.length - 1) 5 hErasedLength64 (by decide) (by
        change fixedArrayBytes (os.length - 1) 5 + 7 < UInt64.size at hBookBytes
        omega)
    have hChoiceCapacity := takeFirstFitFrom_some_capacity hTake
    rw [UInt64.le_iff_toNat_le, hBookNeedNat] at hChoiceCapacity
    have hNewBookCapacity : fixedArrayBytes (os.eraseIdx i).length 5 ≤
        choice.node.capacity.toNat := by
      rw [List.length_eraseIdx_of_lt hi]
      exact hChoiceCapacity
    have hNewBookBelow : choice.node.root.toNat +
        choice.node.capacity.toNat ≤ g0.toNat :=
      hNodesBelow choice.node hChoiceMem
    have hNewBookFree : FreeListSeparatedFromFixedArray choice.remaining
        choice.node.root choice.node.capacity := by
      intro node hNode
      simpa [fixedArrayRegion, FreeNode.region] using
        hList.takeFirstFitFrom_node_disjoint hTake node hNode
    have hBookFree1 : FreeListSeparatedFromFixedArray choice.remaining book
        bookCapacity := by
      intro node hNode
      exact hBookFree node (takeFirstFitFrom_some_remaining_mem hTake hNode)
    have hOldTradesFree1 : FreeListSeparatedFromFixedArray choice.remaining
        oldTrades oldTradesCapacity := by
      intro node hNode
      exact hOldTradesFree node
        (takeFirstFitFrom_some_remaining_mem hTake hNode)
    have hNodesBelow1 : ∀ node ∈ choice.remaining,
        node.root.toNat + node.capacity.toNat ≤ g0.toNat := by
      intro node hNode
      exact hNodesBelow node (takeFirstFitFrom_some_remaining_mem hTake hNode)
    apply FullTradeUpdate.fullTradeUpdateProg_spec env st1
      (BookEraseSuffix.eraseResultFrame base
        (orderArrayBytesU (os.length - 1)) choice.previous choice.node.root
        choice.node.capacity choice.next choice.node.root
        ((os.length - 1 - i) * 5)) fuel choice.node.root
      choice.node.capacity book bookCapacity oldTrades oldTradesCapacity
      remaining g0 (g2 + 1) choice.node.root
      tradeNext oldBookTracker oldTradesTracker taker os (os.eraseIdx i) ts i
      choice.remaining
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame]
        using hParams
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        List.length_set] using hLocals
    · simp [BookEraseSuffix.eraseResultFrame]
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hTakerLocal
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hBookLocal
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hTradesLocal
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hRemainingLocal
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hIndexLocal
    · simp [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals]
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hTradeNextElem
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hFuel
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hOldBookTracker
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hOldTradesTracker
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarryOid
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarryTrader
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarrySide
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarryPrice
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarryQty
    · exact hi
    · exact hOrdersLength64
    · exact hTradeLength64
    · exact hTradeBytes
    · exact hTradeTotalU
    · exact hTradeTotal64
    · exact hTradeTopAtG0
    · exact hTradeFit32AtG0
    · rw [hFinalPages]
      exact hTradeFitAtG0
    · rw [hFinalPages]
      exact hPages
    · exact hOldTrades48
    · exact hOldTrades32
    · exact hOldTradesCapacity
    · exact hOldTradesBelow
    · exact hOldTradesFree1
    · exact hTarget48
    · rw [List.length_eraseIdx_of_lt hi]
      unfold fixedArrayBytes
      omega
    · exact hNewBookCapacity
    · exact hNewBookBelow
    · exact hNewBookFree
    · exact hBook48
    · exact hBook32
    · exact hBookCapacity
    · exact hBookBelow
    · exact hBookFree1
    · exact hNodesBelow1
    · exact hOldTradesOwned1
    · exact hNewBookOwned
    · exact hBookOwned1
    · exact hFinalG0
    · exact hFinalG1
    · exact hFinalG2
    · exact hFinalList
    · intro st2 s newTrades newTradesCapacity nodes2 g0Final hResult
        hNewBookFinal hNewTradesFinal hOldTradesFinal hBookFinal hList2 hG0
        hG1 hG2
      apply hDone st2 s choice.node.root choice.node.capacity newTrades
        newTradesCapacity nodes2 g0Final hResult hNewBookFinal hNewTradesFinal
        hOldTradesFinal hBookFinal hList2 hG0 hG1
      simpa only [hg2Next] using hG2
  · intro previous st1 hTarget48 hTarget32 hNewBookOwned hBookOwned1
      hOldTradesOwned1 hOutside hFinalPages hFinalGlobals hFinalList hFinalG0
      hFinalG1 hFinalG2
    let newBook := g0 + 48
    let bookNeed := orderArrayBytesU (os.length - 1)
    let g0AfterBook := g0 + 48 + bookNeed
    have hBookNeedNat : bookNeed.toNat = orderArrayBytes (os.length - 1) := by
      exact fixedArrayBytesU_toNat (os.length - 1) 5 hErasedLength64
        (by decide) (by
          change fixedArrayBytes (os.length - 1) 5 + 7 < UInt64.size at hBookBytes
          omega)
    have hNewBookNat : newBook.toNat = g0.toNat + 48 := by
      unfold newBook
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48, Nat.mod_eq_of_lt (by omega)]
    have hG0AfterBookNat : g0AfterBook.toNat =
        g0.toNat + 48 + bookNeed.toNat := by
      simpa [g0AfterBook, bookNeed] using hBookTop
    have hNewBookCapacity : fixedArrayBytes (os.eraseIdx i).length 5 ≤
        bookNeed.toNat := by
      rw [List.length_eraseIdx_of_lt hi]
      exact hBookNeedNat.symm.le
    have hNewBookBelow : newBook.toNat + bookNeed.toNat ≤
        g0AfterBook.toNat := by
      rw [hNewBookNat, hG0AfterBookNat]
    have hNewBookFree : FreeListSeparatedFromFixedArray nodes newBook
        bookNeed := by
      intro node hNode
      have hBelow := hNodesBelow node hNode
      obtain ⟨hNode48, _, _⟩ := hList.mem_bounds hNode
      have hStart : newBook.toNat - 48 = g0.toNat := by
        rw [hNewBookNat]
        omega
      unfold regionsDisjoint fixedArrayRegion FreeNode.region
      right
      rw [hStart]
      omega
    have hNodesBelow1 : ∀ node ∈ nodes,
        node.root.toNat + node.capacity.toNat ≤ g0AfterBook.toNat := by
      intro node hNode
      have hBelow := hNodesBelow node hNode
      rw [hG0AfterBookNat]
      omega
    have hBookBelow1 : book.toNat + bookCapacity.toNat ≤
        g0AfterBook.toNat := by
      rw [hG0AfterBookNat]
      omega
    have hOldTradesBelow1 : oldTrades.toNat + oldTradesCapacity.toNat ≤
        g0AfterBook.toNat := by
      rw [hG0AfterBookNat]
      omega
    apply FullTradeUpdate.fullTradeUpdateProg_spec env st1
      (BookEraseSuffix.eraseResultFrame base bookNeed previous 0 g0AfterBook
        ((g0AfterBook - 1) / 65536 + 1) newBook
        ((os.length - 1 - i) * 5)) fuel newBook bookNeed book bookCapacity
      oldTrades oldTradesCapacity remaining g0AfterBook (g2 + 1) newBook
      tradeNext oldBookTracker oldTradesTracker taker os (os.eraseIdx i) ts i
      nodes
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame]
        using hParams
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        List.length_set] using hLocals
    · simp [BookEraseSuffix.eraseResultFrame, newBook]
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hTakerLocal
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hBookLocal
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hTradesLocal
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hRemainingLocal
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hIndexLocal
    · simp [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals, newBook]
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        hLocals] using hTradeNextElem
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hFuel
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hOldBookTracker
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hOldTradesTracker
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarryOid
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarryTrader
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarrySide
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarryPrice
    · simpa [BookEraseSuffix.eraseResultFrame,
        BookErasePrefix.eraseCopyFrame, BookAllocSearch.bookAllocSearchFrame,
        Locals.get, hParams, hLocals] using hCarryQty
    · exact hi
    · exact hOrdersLength64
    · exact hTradeLength64
    · exact hTradeBytes
    · exact hTradeTotalU
    · exact hTradeTotal64
    · simpa [g0AfterBook, bookNeed, add_assoc] using hTradeTopAfterBook
    · simpa [g0AfterBook, bookNeed] using hTradeFit32AfterBook
    · rw [hFinalPages]
      simpa [g0AfterBook, bookNeed] using hTradeFitAfterBook
    · rw [hFinalPages]
      exact hPages
    · exact hOldTrades48
    · exact hOldTrades32
    · exact hOldTradesCapacity
    · exact hOldTradesBelow1
    · exact hOldTradesFree
    · simpa [newBook] using hTarget48
    · change (g0 + 48).toNat + fixedArrayBytes (os.eraseIdx i).length 5 <
        4294967296
      rw [List.length_eraseIdx_of_lt hi]
      unfold fixedArrayBytes
      omega
    · exact hNewBookCapacity
    · exact hNewBookBelow
    · exact hNewBookFree
    · exact hBook48
    · exact hBook32
    · exact hBookCapacity
    · exact hBookBelow1
    · exact hBookFree
    · exact hNodesBelow1
    · exact hOldTradesOwned1
    · simpa [newBook, bookNeed] using hNewBookOwned
    · exact hBookOwned1
    · simpa [g0AfterBook, bookNeed] using hFinalG0
    · exact hFinalG1
    · exact hFinalG2
    · exact hFinalList
    · intro st2 s newTrades newTradesCapacity nodes2 g0Final hResult
        hNewBookFinal hNewTradesFinal hOldTradesFinal hBookFinal hList2 hG0
        hG1 hG2
      apply hDone st2 s newBook bookNeed newTrades newTradesCapacity nodes2
        g0Final hResult
      · simpa [newBook, bookNeed] using hNewBookFinal
      · exact hNewTradesFinal
      · exact hOldTradesFinal
      · exact hBookFinal
      · exact hList2
      · exact hG0
      · exact hG1
      · simpa only [hg2Next] using hG2

end Project.ClobMatchFuel.FullBranch
