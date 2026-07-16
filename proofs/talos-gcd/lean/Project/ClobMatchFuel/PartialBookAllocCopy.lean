import Project.ClobMatchFuel.PartialBookAlloc
import Project.ClobMatchFuel.AllocatorFrame
import Project.ClobMatchFuel.BookReplaceCopy

/-!
# Partial-fill book allocation and copy

This module composes the partial-fill book allocator with the complete source
book copy.  Its continuations retain the allocator outcome used by later
replacement, trade allocation, and release proofs.
-/

namespace Project.ClobMatchFuel.PartialBookAllocCopy

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def partialBookAllocCopyProg : Wasm.Program :=
  PartialBookAlloc.partialBookAllocProg ++ BookReplaceCopy.replaceCopyProg

def fitFrame (base : Locals) (n : Nat) (choice : FreeChoice) : Locals :=
  PartialBookAllocSearch.bookAllocSearchFrame base (orderArrayBytesU n)
    choice.previous choice.node.root choice.node.capacity choice.next
    choice.node.root

def bumpFrame (base : Locals) (n : Nat) (g0 previous : UInt64) : Locals :=
  PartialBookAllocSearch.bookAllocSearchFrame base (orderArrayBytesU n)
    previous 0 (g0 + 48 + orderArrayBytesU n)
    ((g0 + 48 + orderArrayBytesU n - 1) / 65536 + 1) (g0 + 48)

set_option Elab.async false in
theorem partialBookAllocCopyProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (source sourceCapacity g0 g2 capacity next : UInt64)
    (os : List OrderL) (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[57]? = some (.i64 source))
    (hLengthLocal : base.locals[59]? =
      some (.i64 (UInt64.ofNat os.length)))
    (hTotalLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat os.length * 5)))
    (hCapacityLocal : base.locals[73]? = some (.i64 capacity))
    (hNextLocal : base.locals[74]? = some (.i64 next))
    (hn : os.length < UInt64.size)
    (hbytes : orderArrayBytes os.length + 7 < UInt64.size)
    (hTotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5)
    (hTotal64 : os.length * 5 < UInt64.size)
    (htop : (g0 + 48 + orderArrayBytesU os.length).toNat =
      g0.toNat + 48 + (orderArrayBytesU os.length).toNat)
    (hFit32 : g0.toNat + 48 + (orderArrayBytesU os.length).toNat <
      4294967296)
    (hFit : g0.toNat + 48 + (orderArrayBytesU os.length).toNat ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hSourceFree :
      FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hFitDone : ∀ choice : FreeChoice,
      takeFirstFitFrom 0 (orderArrayBytesU os.length) nodes = some choice →
      ∀ st1,
        BookReplaceCopy.replaceCopyInv
            (PartialBookAllocFit.bookAllocFitStore st choice)
            (fitFrame base os.length choice) choice.node.root source g2
            choice.node.capacity os st1
            (BookReplaceCopy.replaceCopyFrame (fitFrame base os.length choice)
              choice.node.root (os.length * 5)) →
        OrdersAt st1 choice.node.root os →
        wp «module» rest Q st1
          (BookReplaceCopy.replaceCopyFrame (fitFrame base os.length choice)
            choice.node.root (os.length * 5)) env)
    (hBumpDone : ∀ previous : UInt64, ∀ st1,
      BookReplaceCopy.replaceCopyInv
          (PartialBookAllocBump.bookAllocBumpStore st g0
            (orderArrayBytesU os.length))
          (bumpFrame base os.length g0 previous) (g0 + 48) source g2
          (orderArrayBytesU os.length) os st1
          (BookReplaceCopy.replaceCopyFrame
            (bumpFrame base os.length g0 previous) (g0 + 48)
            (os.length * 5)) →
      OrdersAt st1 (g0 + 48) os →
      wp «module» rest Q st1
        (BookReplaceCopy.replaceCopyFrame
          (bumpFrame base os.length g0 previous) (g0 + 48)
          (os.length * 5)) env) :
    wp «module» (partialBookAllocCopyProg ++ rest) Q st base env := by
  have hNeedNat : (orderArrayBytesU os.length).toNat =
      orderArrayBytes os.length := by
    exact fixedArrayBytesU_toNat os.length 5 hn (by decide) (by
      change fixedArrayBytes os.length 5 + 7 < UInt64.size at hbytes
      omega)
  have hNeed8 : 8 ≤ (orderArrayBytesU os.length).toNat := by
    rw [hNeedNat]
    unfold orderArrayBytes fixedArrayBytes
    omega
  unfold partialBookAllocCopyProg
  rw [List.append_assoc]
  apply PartialBookAlloc.partialBookAllocProg_spec env st base os.length g0
    capacity next nodes hParams hLocals hValues hLengthLocal hCapacityLocal
    hNextLocal hn hbytes htop hFit32 hFit hPages hg0 hg1 hList Q
    (BookReplaceCopy.replaceCopyProg ++ rest)
  · intro choice hTake
    have hChoiceMem : choice.node ∈ nodes :=
      takeFirstFitFrom_some_mem hTake
    obtain ⟨hTarget48, hTarget32Full, hTargetFitFull⟩ :=
      hList.mem_bounds hChoiceMem
    have hChoiceCapacity := takeFirstFitFrom_some_capacity hTake
    rw [UInt64.le_iff_toNat_le, hNeedNat] at hChoiceCapacity
    have hTarget32 : choice.node.root.toNat +
        (os.length * 5 + 1) * 8 < 4294967296 := by
      unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hFitPages :
        (PartialBookAllocFit.bookAllocFitStore st choice).mem.pages =
          st.mem.pages := by
      simp only [PartialBookAllocFit.bookAllocFitStore,
        BookAllocFit.bookAllocFitStore, BookAllocFit.fixedArrayAllocFitStore,
        BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
        Mem.write64_pages]
      split <;> rfl
    have hTargetFit : choice.node.root.toNat +
        (os.length * 5 + 1) * 8 ≤
          (PartialBookAllocFit.bookAllocFitStore st choice).mem.pages *
            65536 := by
      rw [hFitPages]
      unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hPayloadSep : flatWordsDisjoint
        (flatWordsRegion choice.node.root (os.length * 5))
        (flatWordsRegion source (os.length * 5)) := by
      apply flatWordsDisjoint_of_fixedArrayRegions
        (aCapacity := choice.node.capacity)
        (bCapacity := sourceCapacity) hTarget48 hSource48
      · unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
        omega
      · unfold fixedArrayBytes at hSourceCapacity
        omega
      · simpa [fixedArrayRegion, FreeNode.region] using
          regionsDisjoint_symm (hSourceFree choice.node hChoiceMem)
    have hOwnedFit : OwnedOrderArrayAt
        (PartialBookAllocFit.bookAllocFitStore st choice)
        source sourceCapacity os :=
      ownedOrderArrayAt_fixedArrayAllocFitStore hList hTake hSource48
        hSource32 hSourceCapacity hSourceFree hOwned
    have hg2Fit :
        (PartialBookAllocFit.bookAllocFitStore st choice).globals.globals[2]? =
          some (.i64 g2) := by
      by_cases hPrevious : choice.previous = 0
      · simp only [PartialBookAllocFit.bookAllocFitStore,
          BookAllocFit.bookAllocFitStore, BookAllocFit.fixedArrayAllocFitStore,
          hPrevious, if_pos]
        simpa [List.getElem?_set] using hg2
      · simp [PartialBookAllocFit.bookAllocFitStore,
          BookAllocFit.bookAllocFitStore, BookAllocFit.fixedArrayAllocFitStore,
          hPrevious, hg2]
    apply BookReplaceCopy.replaceCopyProg_spec env
      (PartialBookAllocFit.bookAllocFitStore st choice)
      (fitFrame base os.length choice) choice.node.root source g2
      choice.node.capacity os
    · simpa [fitFrame, PartialBookAllocSearch.bookAllocSearchFrame] using
        hParams
    · simpa [fitFrame, PartialBookAllocSearch.bookAllocSearchFrame,
        List.length_set] using hLocals
    · simpa [fitFrame, PartialBookAllocSearch.bookAllocSearchFrame] using
        hValues
    · simpa [fitFrame, PartialBookAllocSearch.bookAllocSearchFrame,
        List.getElem?_set] using hSourceLocal
    · simpa [fitFrame, PartialBookAllocSearch.bookAllocSearchFrame,
        List.getElem?_set] using hLengthLocal
    · simpa [fitFrame, PartialBookAllocSearch.bookAllocSearchFrame,
        List.getElem?_set] using hTotalLocal
    · simp [fitFrame, PartialBookAllocSearch.bookAllocSearchFrame, hLocals]
    · exact hTotalU
    · exact hTotal64
    · exact hTarget48
    · unfold fixedArrayBytes at hSource32
      omega
    · exact hTarget32
    · exact hTargetFit
    · exact hPayloadSep
    · exact hg2Fit
    · exact BookAllocFit.freshFixedArrayAt_fixedArrayAllocFitStore 5
        hList hTake
    · exact hOwnedFit.2
    · intro st1 hInv hTargetOrders
      exact hFitDone choice hTake st1 hInv hTargetOrders
  · intro previous
    have hTargetNat : (g0 + 48).toNat = g0.toNat + 48 := by
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48, Nat.mod_eq_of_lt (by omega)]
    have hTarget32 : (g0 + 48).toNat +
        (os.length * 5 + 1) * 8 < 4294967296 := by
      have hFit32Nat := hFit32
      rw [hNeedNat] at hFit32Nat
      unfold orderArrayBytes fixedArrayBytes at hFit32Nat
      rw [hTargetNat]
      omega
    have hTargetFit : (g0 + 48).toNat +
        (os.length * 5 + 1) * 8 ≤
          (PartialBookAllocBump.bookAllocBumpStore st g0
            (orderArrayBytesU os.length)).mem.pages * 65536 := by
      have hFitNat := hFit
      rw [hNeedNat] at hFitNat
      unfold orderArrayBytes fixedArrayBytes at hFitNat
      change (g0 + 48).toNat + (os.length * 5 + 1) * 8 ≤
        st.mem.pages * 65536
      rw [hTargetNat]
      omega
    have hPayloadSep : flatWordsDisjoint
        (flatWordsRegion (g0 + 48) (os.length * 5))
        (flatWordsRegion source (os.length * 5)) := by
      unfold flatWordsDisjoint flatWordsRegion
      right
      unfold fixedArrayBytes at hSourceCapacity
      omega
    have hOwnedBump : OwnedOrderArrayAt
        (PartialBookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU os.length)) source sourceCapacity os :=
      ownedOrderArrayAt_fixedArrayAllocBumpStore hFit32 hSource48
        hSource32 hSourceCapacity hSourceBelow hOwned
    have hg2Bump :
        (PartialBookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU os.length)).globals.globals[2]? =
            some (.i64 g2) := by
      simp [PartialBookAllocBump.bookAllocBumpStore,
        BookAllocBump.bookAllocBumpStore,
        BookAllocBump.fixedArrayAllocBumpStore, hg2]
    apply BookReplaceCopy.replaceCopyProg_spec env
      (PartialBookAllocBump.bookAllocBumpStore st g0
        (orderArrayBytesU os.length)) (bumpFrame base os.length g0 previous)
      (g0 + 48) source g2 (orderArrayBytesU os.length) os
    · simpa [bumpFrame, PartialBookAllocSearch.bookAllocSearchFrame] using
        hParams
    · simpa [bumpFrame, PartialBookAllocSearch.bookAllocSearchFrame,
        List.length_set] using hLocals
    · simpa [bumpFrame, PartialBookAllocSearch.bookAllocSearchFrame] using
        hValues
    · simpa [bumpFrame, PartialBookAllocSearch.bookAllocSearchFrame,
        List.getElem?_set] using hSourceLocal
    · simpa [bumpFrame, PartialBookAllocSearch.bookAllocSearchFrame,
        List.getElem?_set] using hLengthLocal
    · simpa [bumpFrame, PartialBookAllocSearch.bookAllocSearchFrame,
        List.getElem?_set] using hTotalLocal
    · simp [bumpFrame, PartialBookAllocSearch.bookAllocSearchFrame, hLocals]
    · exact hTotalU
    · exact hTotal64
    · rw [hTargetNat]
      omega
    · unfold fixedArrayBytes at hSource32
      omega
    · exact hTarget32
    · exact hTargetFit
    · exact hPayloadSep
    · exact hg2Bump
    · exact BookAllocBump.freshFixedArrayAt_fixedArrayAllocBumpStore st g0
        (orderArrayBytesU os.length) 5 hNeed8 hFit32
    · exact hOwnedBump.2
    · intro st1 hInv hTargetOrders
      exact hBumpDone previous st1 hInv hTargetOrders

end Project.ClobMatchFuel.PartialBookAllocCopy
