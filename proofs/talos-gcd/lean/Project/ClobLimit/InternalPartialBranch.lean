import Project.ClobLimit.InternalPartialTradeBranch
import Project.ClobLimit.InternalPartialBookControl

/-!
# Complete internal partial-fill branch

The partial-fill branch replaces the selected maker, appends one trade, and
records a completed recursive result.  This module composes both bump
allocations while retaining the source arrays and bytes below the old heap top.
-/

namespace Project.ClobLimit.InternalPartialBranch

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalPartialBookControl
  Project.ClobLimit.InternalPartialBookPrepare
  Project.ClobLimit.InternalPartialBookUpdate
  Project.ClobLimit.InternalPartialBookCopy
  Project.ClobLimit.InternalPartialBookFinish
  Project.ClobLimit.InternalPartialTradeBranch
  Project.ClobLimit.InternalPartialTradeUpdate
  Project.ClobMatchFuel.AllocatorFrame

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def partialBranchProg : Wasm.Program :=
  partialBookBranchProg partialBookUpdateProg ++ partialTradeBranchProg

set_option Elab.async false in
theorem partialBranchProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (book bookCapacity oldTrades oldTradesCapacity : UInt64)
    (remaining fuel g0 g2 capacity next : UInt64)
    (taker : OrderL) (os : List OrderL) (ts : List TradeL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hFuel : base.get 0 = some (.i64 fuel))
    (hTakerLocal : base.params[1]? = some (.i64 taker.oid))
    (hBookLocal : base.params[7]? = some (.i64 book))
    (hTradesLocal : base.params[9]? = some (.i64 oldTrades))
    (hRemainingLocal : base.params[10]? = some (.i64 remaining))
    (hIndexLocal : base.locals[14]? = some (.i64 (UInt64.ofNat i)))
    (hCapacityLocal : base.locals[61]? = some (.i64 capacity))
    (hNextLocal : base.locals[62]? = some (.i64 next))
    (hi : i < os.length)
    (hOrdersLength64 : os.length < UInt64.size)
    (hBookBytes : fixedArrayBytes os.length 5 + 7 < UInt64.size)
    (hBookTotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5)
    (hBookTotal64 : os.length * 5 < UInt64.size)
    (hBookTop : (g0 + 48 + fixedArrayBytesU os.length 5).toNat =
      g0.toNat + 48 + (fixedArrayBytesU os.length 5).toNat)
    (hBookFit32 : g0.toNat + 48 +
      (fixedArrayBytesU os.length 5).toNat < 4294967296)
    (hBookFit : g0.toNat + 48 +
      (fixedArrayBytesU os.length 5).toNat ≤ st.mem.pages * 65536)
    (hTradeLength64 : ts.length + 1 < UInt64.size)
    (hTradeBytes :
      fixedArrayBytes (ts.length + 1) 4 + 7 < UInt64.size)
    (hTradeTotalU : (UInt64.ofNat ts.length * 4).toNat = ts.length * 4)
    (hTradeTotal64 : ts.length * 4 < UInt64.size)
    (hTradeTop :
      (g0 + 48 + fixedArrayBytesU os.length 5 + 48 +
          fixedArrayBytesU (ts.length + 1) 4).toNat =
        (g0 + 48 + fixedArrayBytesU os.length 5).toNat + 48 +
          (fixedArrayBytesU (ts.length + 1) 4).toNat)
    (hTradeFit32 :
      (g0 + 48 + fixedArrayBytesU os.length 5).toNat + 48 +
          (fixedArrayBytesU (ts.length + 1) 4).toNat < 4294967296)
    (hTradeFit :
      (g0 + 48 + fixedArrayBytesU os.length 5).toNat + 48 +
          (fixedArrayBytesU (ts.length + 1) 4).toNat ≤
        st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hBook48 : 48 ≤ book.toNat)
    (hBook32 : book.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes os.length 5 ≤ bookCapacity.toNat)
    (hBookBelow : book.toNat + bookCapacity.toNat ≤ g0.toNat)
    (hBookOwned : OwnedOrderArrayAt st book bookCapacity os)
    (hOldTrades48 : 48 ≤ oldTrades.toNat)
    (hOldTrades32 : oldTrades.toNat +
      fixedArrayBytes ts.length 4 < 4294967296)
    (hOldTradesCapacity :
      fixedArrayBytes ts.length 4 ≤ oldTradesCapacity.toNat)
    (hOldTradesBelow :
      oldTrades.toNat + oldTradesCapacity.toNat ≤ g0.toNat)
    (hOldTradesOwned :
      OwnedTradeArrayAt st oldTrades oldTradesCapacity ts)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1 s,
      PartialResultAt s (g0 + 48)
        (g0 + 48 + fixedArrayBytesU os.length 5 + 48) fuel →
      OwnedOrderArrayAt st1 book bookCapacity os →
      OwnedOrderArrayAt st1 (g0 + 48) (fixedArrayBytesU os.length 5)
        (Project.ClobMatchFuel.Model.setQtyL os i
          (os[i]!.oqty - remaining)) →
      OwnedTradeArrayAt st1 oldTrades oldTradesCapacity ts →
      OwnedTradeArrayAt st1
        (g0 + 48 + fixedArrayBytesU os.length 5 + 48)
        (fixedArrayBytesU (ts.length + 1) 4)
        (ts ++ [Project.ClobMatchFuel.Model.fillTradeL
          taker os[i]! remaining]) →
      st1.mem.pages = st.mem.pages →
      st1.globals.globals[0]? = some (.i64
        (g0 + 48 + fixedArrayBytesU os.length 5 + 48 +
          fixedArrayBytesU (ts.length + 1) 4)) →
      st1.globals.globals[1]? = some (.i64 0) →
      st1.globals.globals[2]? = some (.i64 (g2 + 2)) →
      (∀ a : Nat, a < g0.toNat → st1.mem.bytes a = st.mem.bytes a) →
      wp «module» rest Q st1 s env) :
    wp «module» (partialBranchProg ++ rest) Q st base env := by
  let qty := os[i]!.oqty - remaining
  let newOrders := Project.ClobMatchFuel.Model.setQtyL os i qty
  let bookNeed := fixedArrayBytesU os.length 5
  let newBook := g0 + 48
  let g0AfterBook := g0 + 48 + bookNeed
  let tradeNeed := fixedArrayBytesU (ts.length + 1) 4
  let newTrades := g0AfterBook + 48
  have hBookNeedNat : bookNeed.toNat = fixedArrayBytes os.length 5 := by
    exact fixedArrayBytesU_toNat os.length 5 hOrdersLength64 (by decide)
      (by omega)
  have hNewBookNat : newBook.toNat = g0.toNat + 48 := by
    unfold newBook
    rw [UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48, Nat.mod_eq_of_lt (by omega)]
  have hG0AfterBookNat : g0AfterBook.toNat =
      g0.toNat + 48 + bookNeed.toNat := by
    simpa [g0AfterBook, bookNeed] using hBookTop
  have hTradeNeedNat : tradeNeed.toNat =
      fixedArrayBytes (ts.length + 1) 4 := by
    exact fixedArrayBytesU_toNat (ts.length + 1) 4 hTradeLength64
      (by decide) (by omega)
  have hNewTradesNat : newTrades.toNat = g0AfterBook.toNat + 48 := by
    unfold newTrades
    rw [UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48, Nat.mod_eq_of_lt (by omega)]
  unfold partialBranchProg
  rw [List.append_assoc]
  apply partialBookBranchProg_spec env st base book remaining os i hParams
    hLocals hValues hBookLocal hIndexLocal hRemainingLocal hi hOrdersLength64
    hBookOwned.2 partialBookUpdateProg Q (partialTradeBranchProg ++ rest)
  apply partialBookUpdateProg_spec env st
    (partialBookPrepareFrame base book remaining os i) book bookCapacity g0
    g2 capacity next qty os i
  · simpa [partialBookPrepareFrame] using hParams
  · simpa [partialBookPrepareFrame, partialBookPrepareLocals,
      List.length_set] using hLocals
  · simp [partialBookPrepareFrame]
  · simp [partialBookPrepareFrame, partialBookPrepareLocals, hLocals]
  · simp [partialBookPrepareFrame, partialBookPrepareLocals, hLocals]
  · simp [partialBookPrepareFrame, partialBookPrepareLocals, hLocals]
  · simp [partialBookPrepareFrame, partialBookPrepareLocals, hLocals]
  · simp [partialBookPrepareFrame, partialBookPrepareLocals, hLocals]
  · simp [partialBookPrepareFrame, partialBookPrepareLocals, hLocals]
  · simp [partialBookPrepareFrame, partialBookPrepareLocals, hLocals]
  · simp [partialBookPrepareFrame, partialBookPrepareLocals, hLocals]
  · simp [partialBookPrepareFrame, partialBookPrepareLocals, qty, hLocals]
  · simpa [partialBookPrepareFrame, partialBookPrepareLocals,
      List.getElem?_set, hLocals] using hCapacityLocal
  · simpa [partialBookPrepareFrame, partialBookPrepareLocals,
      List.getElem?_set, hLocals] using hNextLocal
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
  · exact hBookOwned
  · exact hg0
  · exact hg1
  · exact hg2
  · intro st1 hBookFinal hNewBookFinal hBookOutside hBookPages hBookGlobals
    have hBookAllocPages :
        (partialBookAllocStore st os.length g0).mem.pages = st.mem.pages :=
      Project.Clob.fixedArrayAllocBumpStore_pages st g0 bookNeed 5
    have hBookPagesAlloc : st1.mem.pages =
        (partialBookAllocStore st os.length g0).mem.pages :=
      hBookPages.trans hBookAllocPages.symm
    have hBookTargetSep : regionsDisjoint
        (flatWordsRegion newBook (os.length * 5))
        (fixedArrayRegion oldTrades oldTradesCapacity) := by
      unfold regionsDisjoint flatWordsRegion fixedArrayRegion
      right
      rw [hNewBookNat]
      omega
    have hOldTradesAlloc : OwnedTradeArrayAt
        (partialBookAllocStore st os.length g0)
        oldTrades oldTradesCapacity ts :=
      ownedTradeArrayAt_fixedArrayAllocBumpStore hBookFit32 hOldTrades48
        hOldTrades32 hOldTradesCapacity hOldTradesBelow hOldTradesOwned
    have hOldTradesFinal : OwnedTradeArrayAt st1 oldTrades
        oldTradesCapacity ts :=
      OwnedTradeArrayAt.frame_outsideFlatWords hOldTrades48 hOldTrades32
        hOldTradesCapacity hBookPagesAlloc hBookTargetSep hBookOutside
        hOldTradesAlloc
    have hBookG0 : st1.globals.globals[0]? =
        some (.i64 g0AfterBook) := by
      have hAlloc := Project.Clob.fixedArrayAllocBumpStore_global0 st g0
        bookNeed 5 (.i64 g0) hg0
      rw [hBookGlobals]
      simpa [g0AfterBook, List.getElem?_set] using hAlloc
    have hBookG1 : st1.globals.globals[1]? = some (.i64 0) := by
      have hAlloc := Project.Clob.fixedArrayAllocBumpStore_global_of_ne_zero
        st g0 bookNeed 5 1 (.i64 0) (by decide) hg1
      rw [hBookGlobals]
      simpa [List.getElem?_set] using hAlloc
    have hBookG2 : st1.globals.globals[2]? =
        some (.i64 (g2 + 1)) := by
      have hAlloc := Project.Clob.fixedArrayAllocBumpStore_global_of_ne_zero
        st g0 bookNeed 5 2 (.i64 g2) (by decide) hg2
      have hLength : 2 <
          (partialBookAllocStore st os.length g0).globals.globals.length :=
        (List.getElem?_eq_some_iff.mp hAlloc).1
      rw [hBookGlobals]
      simp [hLength]
    have hNewBook48 : 48 ≤ newBook.toNat := by
      rw [hNewBookNat]
      omega
    have hNewBook32 : newBook.toNat +
        fixedArrayBytes newOrders.length 5 < 4294967296 := by
      rw [hNewBookNat]
      rw [show newOrders.length = os.length by
        simp [newOrders, Project.ClobMatchFuel.Model.setQtyL_length]]
      rw [← hBookNeedNat]
      simpa [bookNeed] using hBookFit32
    have hNewBookCapacity : fixedArrayBytes newOrders.length 5 ≤
        bookNeed.toNat := by
      simp [newOrders, Project.ClobMatchFuel.Model.setQtyL_length,
        hBookNeedNat]
    have hNewBookBelow : newBook.toNat + bookNeed.toNat ≤
        g0AfterBook.toNat := by
      rw [hNewBookNat, hG0AfterBookNat]
    have hBookBelowAfter : book.toNat + bookCapacity.toNat ≤
        g0AfterBook.toNat := by
      rw [hG0AfterBookNat]
      omega
    have hOldTradesBelowAfter : oldTrades.toNat + oldTradesCapacity.toNat ≤
        g0AfterBook.toNat := by
      rw [hG0AfterBookNat]
      omega
    have hPreparedLength :
        (partialBookPrepareFrame base book remaining os i).locals.length =
          64 := by
      simpa [partialBookPrepareFrame, partialBookPrepareLocals,
        List.length_set] using hLocals
    apply Project.BranchPost.oneResultIffPost_of_wp «module» env st1
      (partialBookResultFrame
        (partialBookAllocFrame
          (partialBookPrepareFrame base book remaining os i) os.length g0)
        newBook (os.length * 5)) (partialTradeBranchProg ++ rest) Q
    · simp [partialBookResultFrame]
    apply partialTradeBranchProg_spec env st1
      (partialBookResultFrame
        (partialBookAllocFrame
          (partialBookPrepareFrame base book remaining os i) os.length g0)
        newBook (os.length * 5))
      newBook bookNeed book bookCapacity oldTrades oldTradesCapacity remaining
      fuel g0AfterBook (g2 + 1) 0 g0AfterBook taker os newOrders ts i
    · simpa [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame,
        partialBookPrepareFrame] using hParams
    · simpa [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame,
        partialBookPrepareFrame, partialBookPrepareLocals,
        List.length_set] using hLocals
    · simp [partialBookResultFrame]
    · simpa [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame,
        partialBookPrepareFrame, Locals.get, hParams, hLocals] using hFuel
    · simpa [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame,
        partialBookPrepareFrame] using hTakerLocal
    · simpa [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame,
        partialBookPrepareFrame] using hBookLocal
    · simpa [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame,
        partialBookPrepareFrame] using hTradesLocal
    · simpa [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame,
        partialBookPrepareFrame] using hRemainingLocal
    · simpa [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame,
        partialBookPrepareFrame, partialBookPrepareLocals, hLocals] using
        hIndexLocal
    · simp [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame,
        hPreparedLength]
    · simp [partialBookResultFrame, partialBookCopyFrame,
        partialBookAllocFrame, InternalBookBump.allocFrame, g0AfterBook,
        bookNeed, hPreparedLength]
    · exact hi
    · exact hOrdersLength64
    · exact hTradeLength64
    · exact hTradeBytes
    · exact hTradeTotalU
    · exact hTradeTotal64
    · simpa [g0AfterBook, bookNeed, tradeNeed] using hTradeTop
    · simpa [g0AfterBook, bookNeed, tradeNeed] using hTradeFit32
    · rw [hBookPages]
      simpa [g0AfterBook, bookNeed, tradeNeed] using hTradeFit
    · rw [hBookPages]
      exact hPages
    · exact hBook48
    · exact hBook32
    · exact hBookCapacity
    · exact hBookBelowAfter
    · exact hBookFinal
    · exact hNewBook48
    · exact hNewBook32
    · exact hNewBookCapacity
    · exact hNewBookBelow
    · simpa [newBook, bookNeed, newOrders, qty] using hNewBookFinal
    · exact hOldTrades48
    · exact hOldTrades32
    · exact hOldTradesCapacity
    · exact hOldTradesBelowAfter
    · exact hOldTradesFinal
    · exact hBookG0
    · exact hBookG1
    · exact hBookG2
    · intro st2 s hResult hBookFinal2 hNewBookFinal2 hOldTradesFinal2
        hNewTradesFinal hTradeOutside hTradePages hTradeGlobals
      have hTradeAllocG0 :=
        Project.Clob.fixedArrayAllocBumpStore_global0 st1 g0AfterBook
          tradeNeed 4 (.i64 g0AfterBook) hBookG0
      have hFinalG0 : st2.globals.globals[0]? =
          some (.i64 (g0AfterBook + 48 + tradeNeed)) := by
        rw [hTradeGlobals]
        simpa [List.getElem?_set] using hTradeAllocG0
      have hTradeAllocG1 :=
        Project.Clob.fixedArrayAllocBumpStore_global_of_ne_zero st1
          g0AfterBook tradeNeed 4 1 (.i64 0) (by decide) hBookG1
      have hFinalG1 : st2.globals.globals[1]? = some (.i64 0) := by
        rw [hTradeGlobals]
        simpa [List.getElem?_set] using hTradeAllocG1
      have hTradeAllocG2 :=
        Project.Clob.fixedArrayAllocBumpStore_global_of_ne_zero st1
          g0AfterBook tradeNeed 4 2 (.i64 (g2 + 1)) (by decide) hBookG2
      have hFinalG2 : st2.globals.globals[2]? =
          some (.i64 (g2 + 2)) := by
        rw [hTradeGlobals]
        have hLength : 2 <
            (partialTradeAllocStore st1 (ts.length + 1)
              g0AfterBook).globals.globals.length :=
          (List.getElem?_eq_some_iff.mp hTradeAllocG2).1
        simp only [List.getElem?_set]
        rw [if_pos trivial, if_pos hLength]
        congr 2
        have h2 : (2 : UInt64) = 1 + 1 := by decide
        rw [h2]
        ac_rfl
      have hBelow : ∀ a : Nat, a < g0.toNat →
          st2.mem.bytes a = st.mem.bytes a := by
        intro a ha
        have hBookAllocByte := fixedArrayAllocBumpStore_bytes_below st g0
          bookNeed 5 a hBookFit32 ha
        have hBookFinalByte : st1.mem.bytes a =
            (partialBookAllocStore st os.length g0).mem.bytes a :=
          hBookOutside a (Or.inl (by rw [hNewBookNat]; omega))
        have hTradeAllocByte := fixedArrayAllocBumpStore_bytes_below st1
          g0AfterBook tradeNeed 4 a hTradeFit32 (by
            rw [hG0AfterBookNat]
            omega)
        have hTradeFinalByte : st2.mem.bytes a =
            (partialTradeAllocStore st1 (ts.length + 1)
              g0AfterBook).mem.bytes a :=
          hTradeOutside a (Or.inl (by rw [hNewTradesNat]; omega))
        exact hTradeFinalByte.trans
          (hTradeAllocByte.trans (hBookFinalByte.trans hBookAllocByte))
      apply hDone st2 s
      · simpa [newBook, newTrades, g0AfterBook, bookNeed] using hResult
      · exact hBookFinal2
      · simpa [newBook, bookNeed, newOrders, qty] using hNewBookFinal2
      · exact hOldTradesFinal2
      · simpa [newTrades, g0AfterBook, bookNeed, tradeNeed] using
          hNewTradesFinal
      · exact hTradePages.trans hBookPages
      · simpa [g0AfterBook, bookNeed, tradeNeed] using hFinalG0
      · exact hFinalG1
      · simpa [UInt64.add_assoc] using hFinalG2
      · exact hBelow

end Project.ClobLimit.InternalPartialBranch
