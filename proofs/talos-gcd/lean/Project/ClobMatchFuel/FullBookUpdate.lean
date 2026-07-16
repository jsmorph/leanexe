import Project.ClobMatchFuel.BookAllocErase

/-!
# Full-fill book update

The full-fill book update allocates a smaller order array and copies every
order except the matched maker.  This module retains the allocator outcome,
both source arrays, the represented free list, and the exact allocator globals.
Those facts form the input to the trade-allocation phase.
-/

namespace Project.ClobMatchFuel.FullBookUpdate

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def fullBookUpdateProg : Wasm.Program :=
  BookAllocErase.bookAllocEraseProg

set_option Elab.async false in
theorem fullBookUpdateProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book bookCapacity oldTrades oldTradesCapacity g0 g2 capacity next : UInt64)
    (os : List OrderL) (ts : List TradeL) (i : Nat)
    (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hBookLocal : base.locals[57]? = some (.i64 book))
    (hPrefixLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat (i * 5))))
    (hSuffixLocal : base.locals[61]? =
      some (.i64 (UInt64.ofNat ((os.length - 1 - i) * 5))))
    (hLengthLocal : base.locals[62]? =
      some (.i64 (UInt64.ofNat (os.length - 1))))
    (hCapacityLocal : base.locals[70]? = some (.i64 capacity))
    (hNextLocal : base.locals[71]? = some (.i64 next))
    (hi : i < os.length)
    (hn : os.length - 1 < UInt64.size)
    (hOrderWords64 : os.length * 5 < UInt64.size)
    (hbytes : orderArrayBytes (os.length - 1) + 7 < UInt64.size)
    (htop : (g0 + 48 + orderArrayBytesU (os.length - 1)).toNat =
      g0.toNat + 48 + (orderArrayBytesU (os.length - 1)).toNat)
    (hFit32 : g0.toNat + 48 +
      (orderArrayBytesU (os.length - 1)).toNat < 4294967296)
    (hFit : g0.toNat + 48 +
      (orderArrayBytesU (os.length - 1)).toNat ≤ st.mem.pages * 65536)
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
    (hFitDone : ∀ choice : FreeChoice,
      takeFirstFitFrom 0 (orderArrayBytesU (os.length - 1)) nodes =
          some choice →
      ∀ st1,
        48 ≤ choice.node.root.toNat →
        choice.node.root.toNat + ((os.length - 1) * 5 + 1) * 8 <
          4294967296 →
        OwnedOrderArrayAt st1 choice.node.root choice.node.capacity
          (os.eraseIdx i) →
        OwnedOrderArrayAt st1 book bookCapacity os →
        OwnedTradeArrayAt st1 oldTrades oldTradesCapacity ts →
        MemEqOutsideFlatWords (BookAllocFit.bookAllocFitStore st choice) st1
          choice.node.root ((os.length - 1) * 5) →
        st1.mem.pages = st.mem.pages →
        st1.globals.globals =
          (BookAllocFit.bookAllocFitStore st choice).globals.globals.set 2
            (.i64 (g2 + 1)) →
        FreeListAt st1.mem choice.remaining →
        st1.globals.globals[0]? = some (.i64 g0) →
        st1.globals.globals[1]? =
          some (.i64 (freeHead choice.remaining)) →
        st1.globals.globals[2]? = some (.i64 (g2 + 1)) →
        wp «module» rest Q st1
          (BookEraseSuffix.eraseResultFrame base
            (orderArrayBytesU (os.length - 1)) choice.previous
            choice.node.root choice.node.capacity choice.next choice.node.root
            ((os.length - 1 - i) * 5)) env)
    (hBumpDone : ∀ previous : UInt64, ∀ st1,
      48 ≤ (g0 + 48).toNat →
      (g0 + 48).toNat + ((os.length - 1) * 5 + 1) * 8 <
        4294967296 →
      OwnedOrderArrayAt st1 (g0 + 48)
        (orderArrayBytesU (os.length - 1)) (os.eraseIdx i) →
      OwnedOrderArrayAt st1 book bookCapacity os →
      OwnedTradeArrayAt st1 oldTrades oldTradesCapacity ts →
      MemEqOutsideFlatWords
        (BookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU (os.length - 1))) st1
        (g0 + 48) ((os.length - 1) * 5) →
      st1.mem.pages = st.mem.pages →
      st1.globals.globals =
        (BookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU (os.length - 1))).globals.globals.set 2
            (.i64 (g2 + 1)) →
      FreeListAt st1.mem nodes →
      st1.globals.globals[0]? =
        some (.i64 (g0 + 48 + orderArrayBytesU (os.length - 1))) →
      st1.globals.globals[1]? = some (.i64 (freeHead nodes)) →
      st1.globals.globals[2]? = some (.i64 (g2 + 1)) →
      wp «module» rest Q st1
        (BookEraseSuffix.eraseResultFrame base
          (orderArrayBytesU (os.length - 1)) previous 0
          (g0 + 48 + orderArrayBytesU (os.length - 1))
          ((g0 + 48 + orderArrayBytesU (os.length - 1) - 1) / 65536 + 1)
          (g0 + 48) ((os.length - 1 - i) * 5)) env) :
    wp «module» (fullBookUpdateProg ++ rest) Q st base env := by
  have hNeedNat : (orderArrayBytesU (os.length - 1)).toNat =
      orderArrayBytes (os.length - 1) :=
    fixedArrayBytesU_toNat (os.length - 1) 5 hn (by decide) (by
      change fixedArrayBytes (os.length - 1) 5 + 7 < UInt64.size at hbytes
      omega)
  unfold fullBookUpdateProg
  apply BookAllocErase.bookAllocEraseProg_spec env st base book bookCapacity
    g0 g2 capacity next os i nodes hParams hLocals hValues hBookLocal
    hPrefixLocal hSuffixLocal hLengthLocal hCapacityLocal hNextLocal hi hn
    hOrderWords64 hbytes htop hFit32 hFit hPages hBook48 hBook32
    hBookCapacity hBookBelow hBookFree hBookOwned hg0 hg1 hg2 hList Q rest
  · intro choice hTake st1 hInv hTargetOrders
    obtain ⟨_, _, _, hFinalPagesAlloc, hFinalGlobals, hFresh, _, _, hOutside,
      _, _⟩ := hInv
    have hChoiceMem : choice.node ∈ nodes :=
      takeFirstFitFrom_some_mem hTake
    obtain ⟨hTarget48, _, _⟩ := hList.mem_bounds hChoiceMem
    have hChoiceCapacity := takeFirstFitFrom_some_capacity hTake
    rw [UInt64.le_iff_toNat_le, hNeedNat] at hChoiceCapacity
    have hTarget32 : choice.node.root.toNat +
        ((os.length - 1) * 5 + 1) * 8 < 4294967296 := by
      unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hBookAlloc : OwnedOrderArrayAt
        (BookAllocFit.bookAllocFitStore st choice) book bookCapacity os :=
      ownedOrderArrayAt_fixedArrayAllocFitStore hList hTake hBook48 hBook32
        hBookCapacity hBookFree hBookOwned
    have hOldTradesAlloc : OwnedTradeArrayAt
        (BookAllocFit.bookAllocFitStore st choice) oldTrades
        oldTradesCapacity ts :=
      ownedTradeArrayAt_fixedArrayAllocFitStore hList hTake hOldTrades48
        hOldTrades32 hOldTradesCapacity hOldTradesFree hOldTradesOwned
    have hBookPayloadSep : regionsDisjoint
        (flatWordsRegion choice.node.root ((os.length - 1) * 5))
        (fixedArrayRegion book bookCapacity) := by
      have hSep := hBookFree choice.node hChoiceMem
      unfold regionsDisjoint fixedArrayRegion FreeNode.region at hSep
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hTradePayloadSep : regionsDisjoint
        (flatWordsRegion choice.node.root ((os.length - 1) * 5))
        (fixedArrayRegion oldTrades oldTradesCapacity) := by
      have hSep := hOldTradesFree choice.node hChoiceMem
      unfold regionsDisjoint fixedArrayRegion FreeNode.region at hSep
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hBookFinal := OwnedOrderArrayAt.frame_outsideFlatWords hBook48
      hBook32 hBookCapacity hFinalPagesAlloc hBookPayloadSep hOutside hBookAlloc
    have hOldTradesFinal := OwnedTradeArrayAt.frame_outsideFlatWords
      hOldTrades48 hOldTrades32 hOldTradesCapacity hFinalPagesAlloc
      hTradePayloadSep hOutside hOldTradesAlloc
    have hFinalPages : st1.mem.pages = st.mem.pages :=
      hFinalPagesAlloc.trans (fixedArrayAllocFitStore_pages st choice 5)
    have hFinalList : FreeListAt st1.mem choice.remaining :=
      freeListAt_fixedArrayAllocFitStore_after hList hTake (by
        unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
        omega) hFinalPagesAlloc hOutside
    have hAllocG0 := fixedArrayAllocFitStore_global0
      (choice := choice) (stride := 5) hg0
    have hAllocG1 := fixedArrayAllocFitStore_global1
      (choice := choice) (stride := 5) hg1 hList hTake
    have hFinalG0 : st1.globals.globals[0]? = some (.i64 g0) := by
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG0
    have hFinalG1 : st1.globals.globals[1]? =
        some (.i64 (freeHead choice.remaining)) := by
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG1
    have hAllocG2 :
        (BookAllocFit.bookAllocFitStore st choice).globals.globals[2]? =
          some (.i64 g2) := by
      by_cases hPrevious : choice.previous = 0
      · simp only [BookAllocFit.bookAllocFitStore,
          BookAllocFit.fixedArrayAllocFitStore, hPrevious, if_pos]
        simpa [List.getElem?_set] using hg2
      · simp [BookAllocFit.bookAllocFitStore,
          BookAllocFit.fixedArrayAllocFitStore, hPrevious, hg2]
    have hAllocLength :
        2 < (BookAllocFit.bookAllocFitStore st choice).globals.globals.length :=
      (List.getElem?_eq_some_iff.mp hAllocG2).1
    have hFinalG2 : st1.globals.globals[2]? = some (.i64 (g2 + 1)) := by
      rw [hFinalGlobals]
      simp [hAllocLength]
    exact hFitDone choice hTake st1 hTarget48 hTarget32
      ⟨hFresh, hTargetOrders⟩ hBookFinal hOldTradesFinal hOutside
      hFinalPages hFinalGlobals hFinalList hFinalG0 hFinalG1 hFinalG2
  · intro previous st1 hInv hTargetOrders
    obtain ⟨_, _, _, hFinalPagesAlloc, hFinalGlobals, hFresh, _, _, hOutside,
      _, _⟩ := hInv
    have hTargetNat : (g0 + 48).toNat = g0.toNat + 48 := by
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48, Nat.mod_eq_of_lt (by omega)]
    have hTarget48 : 48 ≤ (g0 + 48).toNat := by
      rw [hTargetNat]
      omega
    have hTarget32 : (g0 + 48).toNat +
        ((os.length - 1) * 5 + 1) * 8 < 4294967296 := by
      have hFit32Nat := hFit32
      rw [hNeedNat] at hFit32Nat
      unfold orderArrayBytes fixedArrayBytes at hFit32Nat
      rw [hTargetNat]
      omega
    have hBookAlloc : OwnedOrderArrayAt
        (BookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU (os.length - 1))) book bookCapacity os :=
      ownedOrderArrayAt_fixedArrayAllocBumpStore hFit32 hBook48 hBook32
        hBookCapacity hBookBelow hBookOwned
    have hOldTradesAlloc : OwnedTradeArrayAt
        (BookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU (os.length - 1))) oldTrades
          oldTradesCapacity ts :=
      ownedTradeArrayAt_fixedArrayAllocBumpStore hFit32 hOldTrades48
        hOldTrades32 hOldTradesCapacity hOldTradesBelow hOldTradesOwned
    have hBookPayloadSep : regionsDisjoint
        (flatWordsRegion (g0 + 48) ((os.length - 1) * 5))
        (fixedArrayRegion book bookCapacity) := by
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      rw [hTargetNat]
      omega
    have hTradePayloadSep : regionsDisjoint
        (flatWordsRegion (g0 + 48) ((os.length - 1) * 5))
        (fixedArrayRegion oldTrades oldTradesCapacity) := by
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      rw [hTargetNat]
      omega
    have hBookFinal := OwnedOrderArrayAt.frame_outsideFlatWords hBook48
      hBook32 hBookCapacity hFinalPagesAlloc hBookPayloadSep hOutside hBookAlloc
    have hOldTradesFinal := OwnedTradeArrayAt.frame_outsideFlatWords
      hOldTrades48 hOldTrades32 hOldTradesCapacity hFinalPagesAlloc
      hTradePayloadSep hOutside hOldTradesAlloc
    have hFinalPages : st1.mem.pages = st.mem.pages :=
      hFinalPagesAlloc.trans (fixedArrayAllocBumpStore_pages st g0
        (orderArrayBytesU (os.length - 1)) 5)
    have hFinalList : FreeListAt st1.mem nodes :=
      freeListAt_fixedArrayAllocBumpStore_after hFit32 hNodesBelow hList
        hFinalPagesAlloc hOutside
    have hAllocG0 := fixedArrayAllocBumpStore_global0 st g0
      (orderArrayBytesU (os.length - 1)) 5 hg0
    have hAllocG1 := fixedArrayAllocBumpStore_global1 st g0
      (orderArrayBytesU (os.length - 1)) 5 (freeHead nodes) hg1
    have hFinalG0 : st1.globals.globals[0]? =
        some (.i64 (g0 + 48 + orderArrayBytesU (os.length - 1))) := by
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG0
    have hFinalG1 : st1.globals.globals[1]? =
        some (.i64 (freeHead nodes)) := by
      rw [hFinalGlobals]
      simpa [List.getElem?_set] using hAllocG1
    have hAllocG2 :
        (BookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU (os.length - 1))).globals.globals[2]? =
            some (.i64 g2) := by
      simp [BookAllocBump.bookAllocBumpStore,
        BookAllocBump.fixedArrayAllocBumpStore, hg2]
    have hAllocLength : 2 <
        (BookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU (os.length - 1))).globals.globals.length :=
      (List.getElem?_eq_some_iff.mp hAllocG2).1
    have hFinalG2 : st1.globals.globals[2]? = some (.i64 (g2 + 1)) := by
      rw [hFinalGlobals]
      simp [hAllocLength]
    exact hBumpDone previous st1 hTarget48 hTarget32
      ⟨hFresh, hTargetOrders⟩ hBookFinal hOldTradesFinal hOutside
      hFinalPages hFinalGlobals hFinalList hFinalG0 hFinalG1 hFinalG2

end Project.ClobMatchFuel.FullBookUpdate
