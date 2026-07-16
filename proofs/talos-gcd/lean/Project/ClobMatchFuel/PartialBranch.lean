import Project.ClobMatchFuel.PartialTradeUpdate

/-!
# Partial-fill branch

The partial-fill branch replaces the matched maker with its reduced quantity,
then appends the resulting trade and exits the loop.  This module composes both
allocators across all four fit and bump combinations.  Its result retains the
two owned output arrays and the allocator state needed by the exported theorem.
-/

namespace Project.ClobMatchFuel.PartialBranch

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def partialBranchProg : Wasm.Program :=
  PartialBookPrepare.partialBookPrepareProg ++
    PartialBookUpdate.partialBookUpdateProg ++
    PartialTradeUpdate.partialTradeUpdateProg

set_option Elab.async false in
theorem partialBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book bookCapacity oldTrades oldTradesCapacity : UInt64)
    (remaining g0 g2 g4 g5 capacity next : UInt64)
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
    (hCapacityLocal : base.locals[73]? = some (.i64 capacity))
    (hNextLocal : base.locals[74]? = some (.i64 next))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hBookBytes : orderArrayBytes os.length + 7 < UInt64.size)
    (hBookTotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5)
    (hBookTotal64 : os.length * 5 < UInt64.size)
    (hBookTop : (g0 + 48 + orderArrayBytesU os.length).toNat =
      g0.toNat + 48 + (orderArrayBytesU os.length).toNat)
    (hBookFit32 : g0.toNat + 48 + (orderArrayBytesU os.length).toNat <
      4294967296)
    (hBookFit : g0.toNat + 48 + (orderArrayBytesU os.length).toNat ≤
      st.mem.pages * 65536)
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
      (g0 + 48 + orderArrayBytesU os.length + 48 +
          tradeArrayBytesU (ts.length + 1)).toNat =
        (g0 + 48 + orderArrayBytesU os.length).toNat + 48 +
          (tradeArrayBytesU (ts.length + 1)).toNat)
    (hTradeFit32AfterBook :
      (g0 + 48 + orderArrayBytesU os.length).toNat + 48 +
          (tradeArrayBytesU (ts.length + 1)).toNat < 4294967296)
    (hTradeFitAfterBook :
      (g0 + 48 + orderArrayBytesU os.length).toNat + 48 +
          (tradeArrayBytesU (ts.length + 1)).toNat ≤
        st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hBook48 : 48 ≤ book.toNat)
    (hBook32 : book.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes os.length 5 ≤ bookCapacity.toNat)
    (hBookBelow : book.toNat + bookCapacity.toNat ≤ g0.toNat)
    (hBookFree :
      FreeListSeparatedFromFixedArray nodes book bookCapacity)
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
    (hg4 : st.globals.globals[4]? = some (.i64 g4))
    (hg5 : st.globals.globals[5]? = some (.i64 g5))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s newBook newBookCapacity newTrades
        newTradesCapacity nodes1 g0Final,
      PartialTradeUpdate.PartialResultAt s newBook newTrades →
      OwnedOrderArrayAt st1 newBook newBookCapacity
        (Model.setQtyL os i (os[i]!.oqty - remaining)) →
      OwnedTradeArrayAt st1 newTrades newTradesCapacity
        (ts ++ [Model.fillTradeL taker os[i]! remaining]) →
      FreeListAt st1.mem nodes1 →
      st1.globals.globals[0]? = some (.i64 g0Final) →
      st1.globals.globals[1]? = some (.i64 (freeHead nodes1)) →
      st1.globals.globals[2]? = some (.i64 (g2 + 2)) →
      st1.globals.globals[4]? = some (.i64 g4) →
      st1.globals.globals[5]? = some (.i64 g5) →
      wp «module» rest Q st1 s env) :
    wp «module» (partialBranchProg ++ rest) Q st base env := by
  let qty := os[i]!.oqty - remaining
  let newOrders := Model.setQtyL os i qty
  have hg2Next : g2 + 1 + 1 = g2 + 2 := by
    have h2 : (2 : UInt64) = 1 + 1 := by decide
    rw [h2]
    ac_rfl
  have hPreparedLength :
      (PartialBookPrepare.partialBookPrepareFrame base book remaining os i).locals.length =
        76 := by
    simpa [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, List.length_set] using
      hLocals
  unfold partialBranchProg
  rw [List.append_assoc, List.append_assoc]
  apply PartialBookPrepare.partialBookPrepareProg_spec env st base book
    remaining os i hParams hLocals hValues hBookLocal hIndexLocal
    hRemainingLocal hi hOrdersLength64 hBookOwned.2 Q
    (PartialBookUpdate.partialBookUpdateProg ++
      PartialTradeUpdate.partialTradeUpdateProg ++ rest)
  apply PartialBookUpdate.partialBookUpdateProg_spec env st
    (PartialBookPrepare.partialBookPrepareFrame base book remaining os i)
    book bookCapacity g0 g2 capacity next qty os i nodes
  · simpa [PartialBookPrepare.partialBookPrepareFrame] using hParams
  · simpa [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, List.length_set] using
      hLocals
  · simp [PartialBookPrepare.partialBookPrepareFrame]
  · simp [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals]
  · simp [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals]
  · simp [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals]
  · simp [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals]
  · simp [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals]
  · simp [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals]
  · simp [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals]
  · simp [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals]
  · simp [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, qty, hLocals]
  · simpa [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals] using
      hCapacityLocal
  · simpa [PartialBookPrepare.partialBookPrepareFrame,
      PartialBookPrepare.partialBookPrepareLocals, hLocals] using hNextLocal
  · exact hi
  · exact hOrdersLength64
  · exact hBookBytes
  · exact hBookTotalU
  · exact hBookTotal64
  · exact hBookTop
  · exact hBookFit32
  · exact hBookFit
  · exact hPages
  · exact hBook48
  · exact hBook32
  · exact hBookCapacity
  · exact hBookBelow
  · exact hBookFree
  · exact hNodesBelow
  · exact hBookOwned
  · exact hg0
  · exact hg1
  · exact hg2
  · exact hList
  · intro choice hTake st1 hTarget48 hTarget32 hTargetFit
      hBookOwnedAlloc hNewBookOwned hOutside hFinalPages hFinalGlobals
      hFinalList hFinalG0 hFinalG1
    let finalStore := BookReplaceStore.replaceOrderStore st1 choice.node.root
      i os[i]! qty
    have hChoiceMem : choice.node ∈ nodes :=
      takeFirstFitFrom_some_mem hTake
    have hBookNeedNat : (orderArrayBytesU os.length).toNat =
        orderArrayBytes os.length :=
      fixedArrayBytesU_toNat os.length 5 hOrdersLength64 (by decide) (by
        change fixedArrayBytes os.length 5 + 7 < UInt64.size at hBookBytes
        omega)
    have hChoiceCapacity := takeFirstFitFrom_some_capacity hTake
    rw [UInt64.le_iff_toNat_le, hBookNeedNat] at hChoiceCapacity
    have hBookPayloadSep : regionsDisjoint
        (flatWordsRegion choice.node.root (os.length * 5))
        (fixedArrayRegion book bookCapacity) := by
      have hSep := hBookFree choice.node hChoiceMem
      unfold regionsDisjoint fixedArrayRegion FreeNode.region at hSep
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hOldTradesAlloc : OwnedTradeArrayAt
        (PartialBookAllocFit.bookAllocFitStore st choice) oldTrades
        oldTradesCapacity ts :=
      ownedTradeArrayAt_fixedArrayAllocFitStore hList hTake hOldTrades48
        hOldTrades32 hOldTradesCapacity hOldTradesFree hOldTradesOwned
    have hTradePayloadSep : regionsDisjoint
        (flatWordsRegion choice.node.root (os.length * 5))
        (fixedArrayRegion oldTrades oldTradesCapacity) := by
      have hSep := hOldTradesFree choice.node hChoiceMem
      unfold regionsDisjoint fixedArrayRegion FreeNode.region at hSep
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hBookOwnedFinal : OwnedOrderArrayAt finalStore book bookCapacity os :=
      OwnedOrderArrayAt.frame_outsideFlatWords hBook48 hBook32
        hBookCapacity hFinalPages hBookPayloadSep hOutside hBookOwnedAlloc
    have hOldTradesFinal : OwnedTradeArrayAt finalStore oldTrades
        oldTradesCapacity ts :=
      OwnedTradeArrayAt.frame_outsideFlatWords hOldTrades48 hOldTrades32
        hOldTradesCapacity hFinalPages hTradePayloadSep hOutside
        hOldTradesAlloc
    have hCurrentPages : finalStore.mem.pages = st.mem.pages := by
      exact hFinalPages.trans (fixedArrayAllocFitStore_pages st choice 5)
    have hCurrentG2 : finalStore.globals.globals[2]? =
        some (.i64 (g2 + 1)) := by
      have hAllocG2 :
          (PartialBookAllocFit.bookAllocFitStore st choice).globals.globals[2]? =
            some (.i64 g2) := by
        by_cases hPrevious : choice.previous = 0
        · simp only [PartialBookAllocFit.bookAllocFitStore,
            BookAllocFit.bookAllocFitStore,
            BookAllocFit.fixedArrayAllocFitStore, hPrevious, if_pos]
          simpa [List.getElem?_set] using hg2
        · simp [PartialBookAllocFit.bookAllocFitStore,
            BookAllocFit.bookAllocFitStore,
            BookAllocFit.fixedArrayAllocFitStore, hPrevious, hg2]
      have hAllocLength : 2 <
          (PartialBookAllocFit.bookAllocFitStore st choice).globals.globals.length :=
        (List.getElem?_eq_some_iff.mp hAllocG2).1
      rw [hFinalGlobals]
      simp [hAllocLength]
    have hCurrentG4 : finalStore.globals.globals[4]? = some (.i64 g4) := by
      have hAllocG4 := fixedArrayAllocFitStore_global_of_ne_one st choice 5
        4 (.i64 g4) (by decide) hg4
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG4
    have hCurrentG5 : finalStore.globals.globals[5]? = some (.i64 g5) := by
      have hAllocG5 := fixedArrayAllocFitStore_global_of_ne_one st choice 5
        5 (.i64 g5) (by decide) hg5
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG5
    have hNewBookCapacity : fixedArrayBytes newOrders.length 5 ≤
        choice.node.capacity.toNat := by
      simpa [newOrders, Model.setQtyL_length] using hChoiceCapacity
    have hNewBookBelow : choice.node.root.toNat +
        choice.node.capacity.toNat ≤ g0.toNat :=
      hNodesBelow choice.node hChoiceMem
    have hNewBookFree : FreeListSeparatedFromFixedArray choice.remaining
        choice.node.root choice.node.capacity := by
      intro node hNode
      simpa [fixedArrayRegion, FreeNode.region] using
        hList.takeFirstFitFrom_node_disjoint hTake node hNode
    have hOldTradesFree1 : FreeListSeparatedFromFixedArray choice.remaining
        oldTrades oldTradesCapacity := by
      intro node hNode
      exact hOldTradesFree node
        (takeFirstFitFrom_some_remaining_mem hTake hNode)
    have hNodesBelow1 : ∀ node ∈ choice.remaining,
        node.root.toNat + node.capacity.toNat ≤ g0.toNat := by
      intro node hNode
      exact hNodesBelow node
        (takeFirstFitFrom_some_remaining_mem hTake hNode)
    apply PartialTradeUpdate.partialTradeUpdateProg_spec env finalStore
      (BookReplaceFinish.replaceResultFrame
        (PartialBookAllocCopy.fitFrame
          (PartialBookPrepare.partialBookPrepareFrame base book remaining os i)
          os.length choice) choice.node.root (os.length * 5))
      choice.node.root choice.node.capacity book oldTrades oldTradesCapacity
      remaining g0 (g2 + 1) g4 g5 choice.node.root choice.node.capacity taker
      os ts i newOrders choice.remaining
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame] using hParams
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, List.length_set] using
        hLocals
    · simp [BookReplaceFinish.replaceResultFrame]
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using hTakerLocal
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using hBookLocal
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using hTradesLocal
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using
        hRemainingLocal
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using hIndexLocal
    · simp [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, hPreparedLength]
    · simp [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, hPreparedLength]
    · exact hi
    · exact hOrdersLength64
    · exact hTradeLength64
    · exact hTradeBytes
    · exact hTradeTotalU
    · exact hTradeTotal64
    · exact hTradeTopAtG0
    · exact hTradeFit32AtG0
    · rw [hCurrentPages]
      exact hTradeFitAtG0
    · rw [hCurrentPages]
      exact hPages
    · exact hOldTrades48
    · exact hOldTrades32
    · exact hOldTradesCapacity
    · exact hOldTradesBelow
    · exact hOldTradesFree1
    · exact hTarget48
    · rw [Model.setQtyL_length]
      unfold fixedArrayBytes
      omega
    · exact hNewBookCapacity
    · exact hNewBookBelow
    · exact hNewBookFree
    · exact hNodesBelow1
    · exact hBookOwnedFinal.2
    · exact hOldTradesFinal
    · exact hNewBookOwned
    · exact hFinalG0
    · exact hFinalG1
    · exact hCurrentG2
    · exact hCurrentG4
    · exact hCurrentG5
    · exact hFinalList
    · intro st2 s newTrades newTradesCapacity nodes2 g0Final hResult
        hNewBookFinal hNewTradesFinal hListFinal hG0Final hG1Final hG2Final
        hG4Final hG5Final
      apply hDone st2 s choice.node.root choice.node.capacity newTrades
        newTradesCapacity nodes2 g0Final hResult
      · simpa [newOrders, qty] using hNewBookFinal
      · exact hNewTradesFinal
      · exact hListFinal
      · exact hG0Final
      · exact hG1Final
      · simpa only [hg2Next] using hG2Final
      · exact hG4Final
      · exact hG5Final
  · intro previous st1 hTarget48 hTarget32 hTargetFit hBookOwnedAlloc
      hNewBookOwned hOutside hFinalPages hFinalGlobals hFinalList hFinalG0
      hFinalG1
    let newBook := g0 + 48
    let bookNeed := orderArrayBytesU os.length
    let g0AfterBook := g0 + 48 + bookNeed
    let finalStore := BookReplaceStore.replaceOrderStore st1 newBook i os[i]!
      qty
    have hBookNeedNat : bookNeed.toNat = orderArrayBytes os.length := by
      exact fixedArrayBytesU_toNat os.length 5 hOrdersLength64 (by decide) (by
        change fixedArrayBytes os.length 5 + 7 < UInt64.size at hBookBytes
        omega)
    have hNewBookNat : newBook.toNat = g0.toNat + 48 := by
      unfold newBook
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48, Nat.mod_eq_of_lt (by omega)]
    have hBookPayloadSep : regionsDisjoint
        (flatWordsRegion newBook (os.length * 5))
        (fixedArrayRegion book bookCapacity) := by
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      rw [hNewBookNat]
      omega
    have hOldTradesAlloc : OwnedTradeArrayAt
        (PartialBookAllocBump.bookAllocBumpStore st g0 bookNeed) oldTrades
        oldTradesCapacity ts :=
      ownedTradeArrayAt_fixedArrayAllocBumpStore hBookFit32 hOldTrades48
        hOldTrades32 hOldTradesCapacity hOldTradesBelow hOldTradesOwned
    have hTradePayloadSep : regionsDisjoint
        (flatWordsRegion newBook (os.length * 5))
        (fixedArrayRegion oldTrades oldTradesCapacity) := by
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      rw [hNewBookNat]
      omega
    have hBookOwnedFinal : OwnedOrderArrayAt finalStore book bookCapacity os :=
      OwnedOrderArrayAt.frame_outsideFlatWords hBook48 hBook32
        hBookCapacity hFinalPages hBookPayloadSep hOutside hBookOwnedAlloc
    have hOldTradesFinal : OwnedTradeArrayAt finalStore oldTrades
        oldTradesCapacity ts :=
      OwnedTradeArrayAt.frame_outsideFlatWords hOldTrades48 hOldTrades32
        hOldTradesCapacity hFinalPages hTradePayloadSep hOutside
        hOldTradesAlloc
    have hCurrentPages : finalStore.mem.pages = st.mem.pages := by
      exact hFinalPages.trans
        (fixedArrayAllocBumpStore_pages st g0 bookNeed 5)
    have hCurrentG2 : finalStore.globals.globals[2]? =
        some (.i64 (g2 + 1)) := by
      have hAllocG2 :
          (PartialBookAllocBump.bookAllocBumpStore st g0
            (orderArrayBytesU os.length)).globals.globals[2]? =
              some (.i64 g2) := by
        simp [PartialBookAllocBump.bookAllocBumpStore,
          BookAllocBump.bookAllocBumpStore,
          BookAllocBump.fixedArrayAllocBumpStore, hg2]
      have hAllocLength : 2 <
          (PartialBookAllocBump.bookAllocBumpStore st g0
            (orderArrayBytesU os.length)).globals.globals.length :=
        (List.getElem?_eq_some_iff.mp hAllocG2).1
      change
        (BookReplaceStore.replaceOrderStore st1 (g0 + 48) i os[i]!
          qty).globals.globals[2]? = some (.i64 (g2 + 1))
      rw [hFinalGlobals]
      simp [hAllocLength]
    have hCurrentG4 : finalStore.globals.globals[4]? = some (.i64 g4) := by
      have hAllocG4 := fixedArrayAllocBumpStore_global_of_ne_zero st g0
        bookNeed 5 4 (.i64 g4) (by decide) hg4
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG4
    have hCurrentG5 : finalStore.globals.globals[5]? = some (.i64 g5) := by
      have hAllocG5 := fixedArrayAllocBumpStore_global_of_ne_zero st g0
        bookNeed 5 5 (.i64 g5) (by decide) hg5
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG5
    have hG0AfterBookNat : g0AfterBook.toNat =
        g0.toNat + 48 + bookNeed.toNat := by
      simpa [g0AfterBook, bookNeed] using hBookTop
    have hNewBookCapacity : fixedArrayBytes newOrders.length 5 ≤
        bookNeed.toNat := by
      simpa [newOrders, Model.setQtyL_length] using hBookNeedNat.symm.le
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
    have hOldTradesBelow1 : oldTrades.toNat + oldTradesCapacity.toNat ≤
        g0AfterBook.toNat := by
      rw [hG0AfterBookNat]
      omega
    apply PartialTradeUpdate.partialTradeUpdateProg_spec env finalStore
      (BookReplaceFinish.replaceResultFrame
        (PartialBookAllocCopy.bumpFrame
          (PartialBookPrepare.partialBookPrepareFrame base book remaining os i)
          os.length g0 previous) newBook (os.length * 5))
      newBook bookNeed book oldTrades oldTradesCapacity remaining g0AfterBook
      (g2 + 1) g4 g5 0 g0AfterBook taker os ts i newOrders nodes
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame] using hParams
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, List.length_set] using
        hLocals
    · simp [BookReplaceFinish.replaceResultFrame]
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using hTakerLocal
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using hBookLocal
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using hTradesLocal
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using
        hRemainingLocal
    · simpa [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame,
        PartialBookPrepare.partialBookPrepareFrame,
        PartialBookPrepare.partialBookPrepareLocals, hLocals] using hIndexLocal
    · simp [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, newBook,
        hPreparedLength]
    · simp [BookReplaceFinish.replaceResultFrame,
        BookReplaceCopy.replaceCopyFrame, PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, g0AfterBook, bookNeed,
        hPreparedLength]
    · exact hi
    · exact hOrdersLength64
    · exact hTradeLength64
    · exact hTradeBytes
    · exact hTradeTotalU
    · exact hTradeTotal64
    · simpa [g0AfterBook, bookNeed, add_assoc] using hTradeTopAfterBook
    · simpa [g0AfterBook, bookNeed] using hTradeFit32AfterBook
    · rw [hCurrentPages]
      simpa [g0AfterBook, bookNeed] using hTradeFitAfterBook
    · rw [hCurrentPages]
      exact hPages
    · exact hOldTrades48
    · exact hOldTrades32
    · exact hOldTradesCapacity
    · exact hOldTradesBelow1
    · exact hOldTradesFree
    · simpa [newBook] using hTarget48
    · change (g0 + 48).toNat + fixedArrayBytes newOrders.length 5 <
        4294967296
      rw [Model.setQtyL_length]
      unfold fixedArrayBytes
      omega
    · exact hNewBookCapacity
    · exact hNewBookBelow
    · exact hNewBookFree
    · exact hNodesBelow1
    · exact hBookOwnedFinal.2
    · exact hOldTradesFinal
    · simpa only [newBook, bookNeed, newOrders] using hNewBookOwned
    · simpa only [finalStore, newBook, g0AfterBook, bookNeed] using hFinalG0
    · exact hFinalG1
    · exact hCurrentG2
    · exact hCurrentG4
    · exact hCurrentG5
    · exact hFinalList
    · intro st2 s newTrades newTradesCapacity nodes2 g0Final hResult
        hNewBookFinal hNewTradesFinal hListFinal hG0Final hG1Final hG2Final
        hG4Final hG5Final
      apply hDone st2 s newBook bookNeed newTrades newTradesCapacity nodes2
        g0Final hResult
      · simpa [newOrders, qty] using hNewBookFinal
      · exact hNewTradesFinal
      · exact hListFinal
      · exact hG0Final
      · exact hG1Final
      · simpa only [hg2Next] using hG2Final
      · exact hG4Final
      · exact hG5Final

end Project.ClobMatchFuel.PartialBranch
