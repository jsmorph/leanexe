import Project.ClobLimit.InternalPartialTradeFinish
import Project.ClobMatchFuel.AllocatorFrame

/-!
# Complete partial-trade update

This module composes empty-list allocation, old-trade copying, and the four
append stores.  Its continuation retains every live array across the new
allocation and target-payload writes.
-/

namespace Project.ClobLimit.InternalPartialTradeUpdate

open Wasm Project.Common Project.Clob Project.Runtime Project.ClobLimit
  Project.ClobLimit.InternalPartialTradeCopy
  Project.ClobLimit.InternalPartialTradeFinish
  Project.ClobMatchFuel.AllocatorFrame
  Project.ClobMatchFuel.TradeAppendStore

def partialTradeAllocFrame (base : Locals) (n : Nat) (g0 : UInt64) :
    Locals :=
  InternalTradeBump.allocFrame base (fixedArrayBytesU n 4) 0 0
    (g0 + 48 + fixedArrayBytesU n 4)
    ((g0 + 48 + fixedArrayBytesU n 4 - 1) / 65536 + 1) (g0 + 48)

abbrev partialTradeAllocStore (st : Store Unit) (n : Nat) (g0 : UInt64) :
    Store Unit :=
  fixedArrayAllocBumpStore st g0 (fixedArrayBytesU n 4) 4

def partialTradeUpdateProg : Wasm.Program :=
  InternalPartialTradeAlloc.partialTradeAllocProg ++
    partialTradeCopyProg ++ partialTradeFinishProg

set_option Elab.async false in
theorem partialTradeUpdateProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (oldBook oldBookCapacity newBook newBookCapacity : UInt64)
    (oldTrades oldTradesCapacity g0 g2 capacity next : UInt64)
    (oldOrders newOrders : List OrderL) (ts : List TradeL) (trade : TradeL)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[45]? = some (.i64 oldTrades))
    (hLengthLocal : base.locals[46]? =
      some (.i64 (UInt64.ofNat ts.length)))
    (hTotalLocal : base.locals[47]? =
      some (.i64 (UInt64.ofNat ts.length * 4)))
    (hNewLengthLocal : base.locals[48]? =
      some (.i64 (UInt64.ofNat (ts.length + 1))))
    (hTakerLocal : base.locals[51]? = some (.i64 trade.ttakerId))
    (hMakerLocal : base.locals[52]? = some (.i64 trade.tmakerId))
    (hPriceLocal : base.locals[53]? = some (.i64 trade.tprice))
    (hQtyLocal : base.locals[54]? = some (.i64 trade.tqty))
    (hCapacityLocal : base.locals[60]? = some (.i64 capacity))
    (hNextLocal : base.locals[61]? = some (.i64 next))
    (hn : ts.length + 1 < UInt64.size)
    (hbytes : fixedArrayBytes (ts.length + 1) 4 + 7 < UInt64.size)
    (hTotalU : (UInt64.ofNat ts.length * 4).toNat = ts.length * 4)
    (hTotal64 : ts.length * 4 < UInt64.size)
    (hTop : (g0 + 48 + fixedArrayBytesU (ts.length + 1) 4).toNat =
      g0.toNat + 48 + (fixedArrayBytesU (ts.length + 1) 4).toNat)
    (hFit32 : g0.toNat + 48 +
      (fixedArrayBytesU (ts.length + 1) 4).toNat < 4294967296)
    (hFit : g0.toNat + 48 +
      (fixedArrayBytesU (ts.length + 1) 4).toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hOldBook48 : 48 ≤ oldBook.toNat)
    (hOldBook32 :
      oldBook.toNat + fixedArrayBytes oldOrders.length 5 < 4294967296)
    (hOldBookCapacity :
      fixedArrayBytes oldOrders.length 5 ≤ oldBookCapacity.toNat)
    (hOldBookBelow : oldBook.toNat + oldBookCapacity.toNat ≤ g0.toNat)
    (hOldBookOwned :
      OwnedOrderArrayAt st oldBook oldBookCapacity oldOrders)
    (hNewBook48 : 48 ≤ newBook.toNat)
    (hNewBook32 :
      newBook.toNat + fixedArrayBytes newOrders.length 5 < 4294967296)
    (hNewBookCapacity :
      fixedArrayBytes newOrders.length 5 ≤ newBookCapacity.toNat)
    (hNewBookBelow : newBook.toNat + newBookCapacity.toNat ≤ g0.toNat)
    (hNewBookOwned :
      OwnedOrderArrayAt st newBook newBookCapacity newOrders)
    (hOldTrades48 : 48 ≤ oldTrades.toNat)
    (hOldTrades32 :
      oldTrades.toNat + fixedArrayBytes ts.length 4 < 4294967296)
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
    (hDone : ∀ st1,
      OwnedOrderArrayAt st1 oldBook oldBookCapacity oldOrders →
      OwnedOrderArrayAt st1 newBook newBookCapacity newOrders →
      OwnedTradeArrayAt st1 oldTrades oldTradesCapacity ts →
      OwnedTradeArrayAt st1 (g0 + 48)
        (fixedArrayBytesU (ts.length + 1) 4) (ts ++ [trade]) →
      MemEqOutsideFlatWords
        (partialTradeAllocStore st (ts.length + 1) g0) st1
        (g0 + 48) ((ts.length + 1) * 4) →
      st1.mem.pages = st.mem.pages →
      st1.globals.globals =
        (partialTradeAllocStore st (ts.length + 1) g0).globals.globals.set 2
          (.i64 (g2 + 1)) →
      wp «module» rest Q st1
        (partialTradeResultFrame
          (partialTradeAllocFrame base (ts.length + 1) g0) (g0 + 48)
          (ts.length * 4)) env) :
    wp «module» (partialTradeUpdateProg ++ rest) Q st base env := by
  have hNeedNat : (fixedArrayBytesU (ts.length + 1) 4).toNat =
      fixedArrayBytes (ts.length + 1) 4 :=
    fixedArrayBytesU_toNat (ts.length + 1) 4 hn (by decide) (by omega)
  have hNeed8 : 8 ≤ (fixedArrayBytesU (ts.length + 1) 4).toNat := by
    rw [hNeedNat]
    unfold fixedArrayBytes
    omega
  have hTargetNat : (g0 + 48).toNat = g0.toNat + 48 := by
    rw [UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48, Nat.mod_eq_of_lt (by omega)]
  have hTarget48 : 48 ≤ (g0 + 48).toNat := by
    rw [hTargetNat]
    omega
  have hOldTradesPayload32 :
      oldTrades.toNat + (ts.length * 4 + 1) * 8 < 4294967296 := by
    unfold fixedArrayBytes at hOldTrades32
    omega
  have hTarget32 : (g0 + 48).toNat +
      ((ts.length + 1) * 4 + 1) * 8 < 4294967296 := by
    rw [hTargetNat]
    rw [hNeedNat] at hFit32
    unfold fixedArrayBytes at hFit32
    omega
  have hTargetFit : (g0 + 48).toNat +
      ((ts.length + 1) * 4 + 1) * 8 ≤
        (partialTradeAllocStore st (ts.length + 1) g0).mem.pages * 65536 := by
    rw [hTargetNat, Project.Clob.fixedArrayAllocBumpStore_pages]
    rw [hNeedNat] at hFit
    unfold fixedArrayBytes at hFit
    omega
  have hPayloadSep : flatWordsDisjoint
      (flatWordsRegion (g0 + 48) ((ts.length + 1) * 4))
      (flatWordsRegion oldTrades (ts.length * 4)) := by
    unfold flatWordsDisjoint flatWordsRegion
    right
    rw [hTargetNat]
    unfold fixedArrayBytes at hOldTradesCapacity
    omega
  have hOldBookRegionSep : regionsDisjoint
      (flatWordsRegion (g0 + 48) ((ts.length + 1) * 4))
      (fixedArrayRegion oldBook oldBookCapacity) := by
    unfold regionsDisjoint flatWordsRegion fixedArrayRegion
    right
    rw [hTargetNat]
    omega
  have hNewBookRegionSep : regionsDisjoint
      (flatWordsRegion (g0 + 48) ((ts.length + 1) * 4))
      (fixedArrayRegion newBook newBookCapacity) := by
    unfold regionsDisjoint flatWordsRegion fixedArrayRegion
    right
    rw [hTargetNat]
    omega
  have hOldTradesRegionSep : regionsDisjoint
      (flatWordsRegion (g0 + 48) ((ts.length + 1) * 4))
      (fixedArrayRegion oldTrades oldTradesCapacity) := by
    unfold regionsDisjoint flatWordsRegion fixedArrayRegion
    right
    rw [hTargetNat]
    omega
  have hOldBookAlloc : OwnedOrderArrayAt
      (partialTradeAllocStore st (ts.length + 1) g0)
      oldBook oldBookCapacity oldOrders :=
    ownedOrderArrayAt_fixedArrayAllocBumpStore hFit32 hOldBook48 hOldBook32
      hOldBookCapacity hOldBookBelow hOldBookOwned
  have hNewBookAlloc : OwnedOrderArrayAt
      (partialTradeAllocStore st (ts.length + 1) g0)
      newBook newBookCapacity newOrders :=
    ownedOrderArrayAt_fixedArrayAllocBumpStore hFit32 hNewBook48 hNewBook32
      hNewBookCapacity hNewBookBelow hNewBookOwned
  have hOldTradesAlloc : OwnedTradeArrayAt
      (partialTradeAllocStore st (ts.length + 1) g0)
      oldTrades oldTradesCapacity ts :=
    ownedTradeArrayAt_fixedArrayAllocBumpStore hFit32 hOldTrades48
      hOldTrades32 hOldTradesCapacity hOldTradesBelow hOldTradesOwned
  have hg2Alloc :
      (partialTradeAllocStore st (ts.length + 1) g0).globals.globals[2]? =
        some (.i64 g2) :=
    Project.Clob.fixedArrayAllocBumpStore_global_of_ne_zero st g0
      (fixedArrayBytesU (ts.length + 1) 4) 4 2 (.i64 g2) (by decide) hg2
  have hFresh : FreshFixedArrayAt
      (partialTradeAllocStore st (ts.length + 1) g0) (g0 + 48)
      (fixedArrayBytesU (ts.length + 1) 4) 4 :=
    Project.Clob.fixedArrayAllocBumpStore_spec st g0
      (fixedArrayBytesU (ts.length + 1) 4) 4 hNeed8 hFit32
  unfold partialTradeUpdateProg
  rw [List.append_assoc, List.append_assoc]
  apply InternalPartialTradeAlloc.partialTradeAllocProg_spec env st base
    (ts.length + 1) g0 capacity next hParams hLocals hValues hNewLengthLocal
    hCapacityLocal hNextLocal hn hbytes hTop hFit32 hFit hPages hg0 hg1 Q
      (partialTradeCopyProg ++ partialTradeFinishProg ++ rest)
  apply partialTradeCopyProg_spec env
    (partialTradeAllocStore st (ts.length + 1) g0)
    (partialTradeAllocFrame base (ts.length + 1) g0) (g0 + 48) oldTrades
    g2 (fixedArrayBytesU (ts.length + 1) 4)
    (UInt64.ofNat (ts.length + 1)) ts
  · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame] using hParams
  · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
      List.length_set] using hLocals
  · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame] using hValues
  · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
      List.getElem?_set] using hSourceLocal
  · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
      List.getElem?_set] using hTotalLocal
  · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
      List.getElem?_set] using hNewLengthLocal
  · simp [partialTradeAllocFrame, InternalTradeBump.allocFrame, hLocals]
  · exact hTotalU
  · exact hTotal64
  · exact hTarget48
  · exact hOldTradesPayload32
  · exact hTarget32
  · exact hTargetFit
  · exact hPayloadSep
  · exact hg2Alloc
  · exact hFresh
  · exact hOldTradesAlloc.2
  · intro st1 hInv
    have hState := hInv
    obtain ⟨_, _, _, hCopyPages, hCopyGlobals, _, _, _, _, _⟩ := hState
    apply partialTradeFinishProg_spec env
      (partialTradeAllocStore st (ts.length + 1) g0) st1
      (partialTradeAllocFrame base (ts.length + 1) g0) (g0 + 48)
      oldTrades g2 (fixedArrayBytesU (ts.length + 1) 4) ts trade
    · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame] using hParams
    · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
        List.length_set] using hLocals
    · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
        List.getElem?_set] using hLengthLocal
    · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
        List.getElem?_set] using hTakerLocal
    · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
        List.getElem?_set] using hMakerLocal
    · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
        List.getElem?_set] using hPriceLocal
    · simpa [partialTradeAllocFrame, InternalTradeBump.allocFrame,
        List.getElem?_set] using hQtyLocal
    · exact hTarget48
    · exact hTarget32
    · exact hTargetFit
    · exact hOldTradesAlloc.2
    · exact hInv
    · intro hTargetFinal hFreshFinal hOutsideFinal
      have hFinalPagesAlloc :
          (appendTradeStore st1 (g0 + 48) ts.length trade).mem.pages =
            (partialTradeAllocStore st (ts.length + 1) g0).mem.pages := by
        simpa [appendTradeStore] using hCopyPages
      have hFinalPages :
          (appendTradeStore st1 (g0 + 48) ts.length trade).mem.pages =
            st.mem.pages :=
        hFinalPagesAlloc.trans
          (Project.Clob.fixedArrayAllocBumpStore_pages st g0
            (fixedArrayBytesU (ts.length + 1) 4) 4)
      have hFinalGlobals :
          (appendTradeStore st1 (g0 + 48) ts.length trade).globals.globals =
            (partialTradeAllocStore st (ts.length + 1) g0).globals.globals.set
              2 (.i64 (g2 + 1)) := by
        simpa [appendTradeStore] using hCopyGlobals
      have hOldBookFinal : OwnedOrderArrayAt
          (appendTradeStore st1 (g0 + 48) ts.length trade)
          oldBook oldBookCapacity oldOrders :=
        OwnedOrderArrayAt.frame_outsideFlatWords hOldBook48 hOldBook32
          hOldBookCapacity hFinalPagesAlloc hOldBookRegionSep hOutsideFinal
          hOldBookAlloc
      have hNewBookFinal : OwnedOrderArrayAt
          (appendTradeStore st1 (g0 + 48) ts.length trade)
          newBook newBookCapacity newOrders :=
        OwnedOrderArrayAt.frame_outsideFlatWords hNewBook48 hNewBook32
          hNewBookCapacity hFinalPagesAlloc hNewBookRegionSep hOutsideFinal
          hNewBookAlloc
      have hOldTradesFinal : OwnedTradeArrayAt
          (appendTradeStore st1 (g0 + 48) ts.length trade)
          oldTrades oldTradesCapacity ts :=
        OwnedTradeArrayAt.frame_outsideFlatWords hOldTrades48 hOldTrades32
          hOldTradesCapacity hFinalPagesAlloc hOldTradesRegionSep hOutsideFinal
          hOldTradesAlloc
      exact hDone _ hOldBookFinal hNewBookFinal hOldTradesFinal
        ⟨hFreshFinal, hTargetFinal⟩ hOutsideFinal hFinalPages hFinalGlobals

end Project.ClobLimit.InternalPartialTradeUpdate
