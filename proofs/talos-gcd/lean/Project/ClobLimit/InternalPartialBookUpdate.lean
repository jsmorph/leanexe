import Project.ClobLimit.InternalPartialBookFinish
import Project.ClobMatchFuel.AllocatorFrame

/-!
# Complete partial-book update

This module composes empty-list allocation, complete source copying, and the
five maker-field stores.  Its continuation retains ownership of both the
source and replacement books together with the allocator memory frame.
-/

namespace Project.ClobLimit.InternalPartialBookUpdate

open Wasm Project.Common Project.Clob Project.Runtime Project.ClobLimit
  Project.ClobLimit.InternalPartialBookCopy
  Project.ClobLimit.InternalPartialBookFinish
  Project.ClobMatchFuel.AllocatorFrame
  Project.ClobMatchFuel.BookReplaceStore

def partialBookAllocFrame (base : Locals) (n : Nat) (g0 : UInt64) :
    Locals :=
  InternalBookBump.allocFrame base (fixedArrayBytesU n 5) 0 0
    (g0 + 48 + fixedArrayBytesU n 5)
    ((g0 + 48 + fixedArrayBytesU n 5 - 1) / 65536 + 1) (g0 + 48)

abbrev partialBookAllocStore (st : Store Unit) (n : Nat) (g0 : UInt64) :
    Store Unit :=
  fixedArrayAllocBumpStore st g0 (fixedArrayBytesU n 5) 5

def partialBookUpdateProg : Wasm.Program :=
  InternalPartialBookAlloc.partialBookAllocProg ++
    partialBookCopyProg ++ partialBookFinishProg

set_option Elab.async false in
theorem partialBookUpdateProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (source sourceCapacity g0 g2 capacity next qty : UInt64)
    (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[45]? = some (.i64 source))
    (hIndexLocal : base.locals[46]? = some (.i64 (UInt64.ofNat i)))
    (hLengthLocal : base.locals[47]? =
      some (.i64 (UInt64.ofNat os.length)))
    (hTotalLocal : base.locals[48]? =
      some (.i64 (UInt64.ofNat os.length * 5)))
    (hOidLocal : base.locals[51]? = some (.i64 os[i]!.oid))
    (hTraderLocal : base.locals[52]? = some (.i64 os[i]!.otrader))
    (hSideLocal : base.locals[53]? = some (.i64 os[i]!.oside))
    (hPriceLocal : base.locals[54]? = some (.i64 os[i]!.oprice))
    (hQtyLocal : base.locals[55]? = some (.i64 qty))
    (hCapacityLocal : base.locals[61]? = some (.i64 capacity))
    (hNextLocal : base.locals[62]? = some (.i64 next))
    (hi : i < os.length)
    (hn : os.length < UInt64.size)
    (hbytes : fixedArrayBytes os.length 5 + 7 < UInt64.size)
    (hTotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5)
    (hTotal64 : os.length * 5 < UInt64.size)
    (hTop : (g0 + 48 + fixedArrayBytesU os.length 5).toNat =
      g0.toNat + 48 + (fixedArrayBytesU os.length 5).toNat)
    (hFit32 : g0.toNat + 48 +
      (fixedArrayBytesU os.length 5).toNat < 4294967296)
    (hFit : g0.toNat + 48 +
      (fixedArrayBytesU os.length 5).toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1,
      OwnedOrderArrayAt st1 source sourceCapacity os →
      OwnedOrderArrayAt st1 (g0 + 48) (fixedArrayBytesU os.length 5)
        (Project.ClobMatchFuel.Model.setQtyL os i qty) →
      MemEqOutsideFlatWords (partialBookAllocStore st os.length g0) st1
        (g0 + 48) (os.length * 5) →
      st1.mem.pages = st.mem.pages →
      st1.globals.globals =
        (partialBookAllocStore st os.length g0).globals.globals.set 2
          (.i64 (g2 + 1)) →
      wp «module» rest Q st1
        (partialBookResultFrame
          (partialBookAllocFrame base os.length g0) (g0 + 48)
          (os.length * 5)) env) :
    wp «module» (partialBookUpdateProg ++ rest) Q st base env := by
  have hNeedNat : (fixedArrayBytesU os.length 5).toNat =
      fixedArrayBytes os.length 5 :=
    fixedArrayBytesU_toNat os.length 5 hn (by decide) (by omega)
  have hNeed8 : 8 ≤ (fixedArrayBytesU os.length 5).toNat := by
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
  have hSourcePayload32 :
      source.toNat + (os.length * 5 + 1) * 8 < 4294967296 := by
    unfold fixedArrayBytes at hSource32
    omega
  have hTarget32 : (g0 + 48).toNat +
      (os.length * 5 + 1) * 8 < 4294967296 := by
    rw [hTargetNat]
    rw [hNeedNat] at hFit32
    unfold fixedArrayBytes at hFit32
    omega
  have hTargetFit : (g0 + 48).toNat +
      (os.length * 5 + 1) * 8 ≤
        (partialBookAllocStore st os.length g0).mem.pages * 65536 := by
    rw [hTargetNat, Project.Clob.fixedArrayAllocBumpStore_pages]
    rw [hNeedNat] at hFit
    unfold fixedArrayBytes at hFit
    omega
  have hPayloadSep : flatWordsDisjoint
      (flatWordsRegion (g0 + 48) (os.length * 5))
      (flatWordsRegion source (os.length * 5)) := by
    unfold flatWordsDisjoint flatWordsRegion
    right
    rw [hTargetNat]
    unfold fixedArrayBytes at hSourceCapacity
    omega
  have hSourceRegionSep : regionsDisjoint
      (flatWordsRegion (g0 + 48) (os.length * 5))
      (fixedArrayRegion source sourceCapacity) := by
    unfold regionsDisjoint flatWordsRegion fixedArrayRegion
    right
    rw [hTargetNat]
    omega
  have hOwnedAlloc : OwnedOrderArrayAt
      (partialBookAllocStore st os.length g0) source sourceCapacity os :=
    ownedOrderArrayAt_fixedArrayAllocBumpStore hFit32 hSource48 hSource32
      hSourceCapacity hSourceBelow hOwned
  have hg2Alloc :
      (partialBookAllocStore st os.length g0).globals.globals[2]? =
        some (.i64 g2) :=
    Project.Clob.fixedArrayAllocBumpStore_global_of_ne_zero st g0
      (fixedArrayBytesU os.length 5) 5 2 (.i64 g2) (by decide) hg2
  have hFresh : FreshFixedArrayAt
      (partialBookAllocStore st os.length g0) (g0 + 48)
      (fixedArrayBytesU os.length 5) 5 :=
    Project.Clob.fixedArrayAllocBumpStore_spec st g0
      (fixedArrayBytesU os.length 5) 5 hNeed8 hFit32
  unfold partialBookUpdateProg
  rw [List.append_assoc, List.append_assoc]
  apply InternalPartialBookAlloc.partialBookAllocProg_spec env st base os.length
    g0 capacity next hParams hLocals hValues hLengthLocal hCapacityLocal
    hNextLocal hn hbytes hTop hFit32 hFit hPages hg0 hg1 Q
      (partialBookCopyProg ++ partialBookFinishProg ++ rest)
  apply partialBookCopyProg_spec env (partialBookAllocStore st os.length g0)
    (partialBookAllocFrame base os.length g0) (g0 + 48) source g2
    (fixedArrayBytesU os.length 5) os
  · simpa [partialBookAllocFrame, InternalBookBump.allocFrame] using hParams
  · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
      List.length_set] using hLocals
  · simpa [partialBookAllocFrame, InternalBookBump.allocFrame] using hValues
  · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
      List.getElem?_set] using hSourceLocal
  · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
      List.getElem?_set] using hLengthLocal
  · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
      List.getElem?_set] using hTotalLocal
  · simp [partialBookAllocFrame, InternalBookBump.allocFrame, hLocals]
  · exact hTotalU
  · exact hTotal64
  · exact hTarget48
  · exact hSourcePayload32
  · exact hTarget32
  · exact hTargetFit
  · exact hPayloadSep
  · exact hg2Alloc
  · exact hFresh
  · exact hOwnedAlloc.2
  · intro st1 hInv hTargetOrders
    have hState := hInv
    obtain ⟨_, _, _, hCopyPages, hCopyGlobals, _, _, _, _, _⟩ := hState
    apply partialBookFinishProg_spec env
      (partialBookAllocStore st os.length g0) st1
      (partialBookAllocFrame base os.length g0) (g0 + 48) source g2
      (fixedArrayBytesU os.length 5) qty os i
    · simpa [partialBookAllocFrame, InternalBookBump.allocFrame] using hParams
    · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
        List.length_set] using hLocals
    · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
        List.getElem?_set] using hIndexLocal
    · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
        List.getElem?_set] using hOidLocal
    · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
        List.getElem?_set] using hTraderLocal
    · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
        List.getElem?_set] using hSideLocal
    · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
        List.getElem?_set] using hPriceLocal
    · simpa [partialBookAllocFrame, InternalBookBump.allocFrame,
        List.getElem?_set] using hQtyLocal
    · exact hi
    · exact hTarget48
    · exact hTarget32
    · exact hInv
    · exact hTargetOrders
    · intro hTargetFinal hFreshFinal hOutsideFinal
      have hFinalPagesAlloc :
          (replaceOrderStore st1 (g0 + 48) i os[i]! qty).mem.pages =
            (partialBookAllocStore st os.length g0).mem.pages := by
        simpa [replaceOrderStore] using hCopyPages
      have hFinalPages :
          (replaceOrderStore st1 (g0 + 48) i os[i]! qty).mem.pages =
            st.mem.pages :=
        hFinalPagesAlloc.trans
          (Project.Clob.fixedArrayAllocBumpStore_pages st g0
            (fixedArrayBytesU os.length 5) 5)
      have hFinalGlobals :
          (replaceOrderStore st1 (g0 + 48) i os[i]! qty).globals.globals =
            (partialBookAllocStore st os.length g0).globals.globals.set 2
              (.i64 (g2 + 1)) := by
        simpa [replaceOrderStore] using hCopyGlobals
      have hSourceFinal : OwnedOrderArrayAt
          (replaceOrderStore st1 (g0 + 48) i os[i]! qty)
          source sourceCapacity os :=
        OwnedOrderArrayAt.frame_outsideFlatWords hSource48 hSource32
          hSourceCapacity hFinalPagesAlloc hSourceRegionSep hOutsideFinal
          hOwnedAlloc
      exact hDone _ hSourceFinal ⟨hFreshFinal, hTargetFinal⟩ hOutsideFinal
        hFinalPages hFinalGlobals

end Project.ClobLimit.InternalPartialBookUpdate
