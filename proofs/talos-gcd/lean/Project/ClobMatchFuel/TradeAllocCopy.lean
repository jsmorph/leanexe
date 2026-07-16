import Project.ClobMatchFuel.TradeAlloc
import Project.ClobMatchFuel.AllocatorFrame
import Project.ClobMatchFuel.TradeAppendCopy

/-!
# Trade allocation and prefix copy

This module composes the common trade allocator with the old-trade copy.  Its
continuations retain the allocator outcome needed by the later release proof.
-/

namespace Project.ClobMatchFuel.TradeAllocCopy

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def tradeAllocCopyProg : Wasm.Program :=
  TradeAlloc.tradeAllocProg ++ TradeAppendCopy.tradeCopyProg

set_option Elab.async false in
theorem tradeAllocCopyProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (source sourceCapacity g0 g2 capacity next : UInt64)
    (ts : List TradeL) (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[57]? = some (.i64 source))
    (hTotalLocal : base.locals[59]? =
      some (.i64 (UInt64.ofNat ts.length * 4)))
    (hLengthLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat (ts.length + 1))))
    (hCapacityLocal : base.locals[72]? = some (.i64 capacity))
    (hNextLocal : base.locals[73]? = some (.i64 next))
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
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hSourceFree :
      FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (hOwned : OwnedTradeArrayAt st source sourceCapacity ts)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hFitDone : ∀ choice : FreeChoice,
      takeFirstFitFrom 0 (tradeArrayBytesU (ts.length + 1)) nodes =
          some choice →
      ∀ st1,
        TradeAppendCopy.tradeCopyInv
            (TradeAllocFit.tradeAllocFitStore st choice)
            (TradeAllocSearch.tradeAllocSearchFrame base
              (tradeArrayBytesU (ts.length + 1)) choice.previous
              choice.node.root choice.node.capacity choice.next
              choice.node.root)
            choice.node.root source g2 choice.node.capacity
            (UInt64.ofNat (ts.length + 1)) ts st1
            (TradeAppendCopy.tradeCopyFrame
              (TradeAllocSearch.tradeAllocSearchFrame base
                (tradeArrayBytesU (ts.length + 1)) choice.previous
                choice.node.root choice.node.capacity choice.next
                choice.node.root)
              choice.node.root (ts.length * 4)) →
        wp «module» rest Q st1
          (TradeAppendCopy.tradeCopyFrame
            (TradeAllocSearch.tradeAllocSearchFrame base
              (tradeArrayBytesU (ts.length + 1)) choice.previous
              choice.node.root choice.node.capacity choice.next
              choice.node.root)
            choice.node.root (ts.length * 4)) env)
    (hBumpDone : ∀ previous : UInt64, ∀ st1,
      TradeAppendCopy.tradeCopyInv
          (TradeAllocBump.tradeAllocBumpStore st g0
            (tradeArrayBytesU (ts.length + 1)))
          (TradeAllocSearch.tradeAllocSearchFrame base
            (tradeArrayBytesU (ts.length + 1)) previous 0
            (g0 + 48 + tradeArrayBytesU (ts.length + 1))
            ((g0 + 48 + tradeArrayBytesU (ts.length + 1) - 1) /
              65536 + 1)
            (g0 + 48))
          (g0 + 48) source g2 (tradeArrayBytesU (ts.length + 1))
          (UInt64.ofNat (ts.length + 1)) ts st1
          (TradeAppendCopy.tradeCopyFrame
            (TradeAllocSearch.tradeAllocSearchFrame base
              (tradeArrayBytesU (ts.length + 1)) previous 0
              (g0 + 48 + tradeArrayBytesU (ts.length + 1))
              ((g0 + 48 + tradeArrayBytesU (ts.length + 1) - 1) /
                65536 + 1)
              (g0 + 48))
            (g0 + 48) (ts.length * 4)) →
      wp «module» rest Q st1
        (TradeAppendCopy.tradeCopyFrame
          (TradeAllocSearch.tradeAllocSearchFrame base
            (tradeArrayBytesU (ts.length + 1)) previous 0
            (g0 + 48 + tradeArrayBytesU (ts.length + 1))
            ((g0 + 48 + tradeArrayBytesU (ts.length + 1) - 1) /
              65536 + 1)
            (g0 + 48))
          (g0 + 48) (ts.length * 4)) env) :
    wp «module» (tradeAllocCopyProg ++ rest) Q st base env := by
  have hNeedNat : (tradeArrayBytesU (ts.length + 1)).toNat =
      tradeArrayBytes (ts.length + 1) := by
    exact fixedArrayBytesU_toNat (ts.length + 1) 4 hn (by decide)
      (by
        change fixedArrayBytes (ts.length + 1) 4 + 7 < UInt64.size at hbytes
        omega)
  have hNeed8 : 8 ≤ (tradeArrayBytesU (ts.length + 1)).toNat := by
    rw [hNeedNat]
    unfold tradeArrayBytes fixedArrayBytes
    omega
  unfold tradeAllocCopyProg
  rw [List.append_assoc]
  apply TradeAlloc.tradeAllocProg_spec env st base (ts.length + 1) g0
    capacity next nodes hParams hLocals hValues hLengthLocal hCapacityLocal
    hNextLocal hn hbytes htop hFit32 hFit hPages hg0 hg1 hList Q
    (TradeAppendCopy.tradeCopyProg ++ rest)
  · intro choice hTake
    let allocBase := TradeAllocSearch.tradeAllocSearchFrame base
      (tradeArrayBytesU (ts.length + 1)) choice.previous choice.node.root
      choice.node.capacity choice.next choice.node.root
    have hChoiceMem : choice.node ∈ nodes :=
      takeFirstFitFrom_some_mem hTake
    obtain ⟨hTarget48, hTarget32Full, hTargetFitFull⟩ :=
      hList.mem_bounds hChoiceMem
    have hChoiceCapacity := takeFirstFitFrom_some_capacity hTake
    rw [UInt64.le_iff_toNat_le, hNeedNat] at hChoiceCapacity
    have hTarget32 : choice.node.root.toNat +
        ((ts.length + 1) * 4 + 1) * 8 < 4294967296 := by
      unfold tradeArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hFitPages :
        (TradeAllocFit.tradeAllocFitStore st choice).mem.pages =
          st.mem.pages := by
      simp only [TradeAllocFit.tradeAllocFitStore,
        BookAllocFit.fixedArrayAllocFitStore,
        BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
        Mem.write64_pages]
      split <;> rfl
    have hTargetFit : choice.node.root.toNat +
        ((ts.length + 1) * 4 + 1) * 8 ≤
          (TradeAllocFit.tradeAllocFitStore st choice).mem.pages * 65536 := by
      rw [hFitPages]
      unfold tradeArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hPayloadSep : flatWordsDisjoint
        (flatWordsRegion choice.node.root ((ts.length + 1) * 4))
        (flatWordsRegion source (ts.length * 4)) := by
      apply flatWordsDisjoint_of_fixedArrayRegions
        (aCapacity := choice.node.capacity)
        (bCapacity := sourceCapacity) hTarget48 hSource48
      · unfold tradeArrayBytes fixedArrayBytes at hChoiceCapacity
        omega
      · unfold fixedArrayBytes at hSourceCapacity
        omega
      · simpa [fixedArrayRegion, FreeNode.region] using
          regionsDisjoint_symm (hSourceFree choice.node hChoiceMem)
    have hOwnedFit : OwnedTradeArrayAt
        (TradeAllocFit.tradeAllocFitStore st choice) source sourceCapacity ts :=
      ownedTradeArrayAt_fixedArrayAllocFitStore hList hTake hSource48
        hSource32 hSourceCapacity hSourceFree hOwned
    have hg2Fit :
        (TradeAllocFit.tradeAllocFitStore st choice).globals.globals[2]? =
          some (.i64 g2) := by
      by_cases hPrevious : choice.previous = 0
      · simp only [TradeAllocFit.tradeAllocFitStore,
          BookAllocFit.fixedArrayAllocFitStore, hPrevious, if_pos]
        simpa [List.getElem?_set] using hg2
      · simp [TradeAllocFit.tradeAllocFitStore,
          BookAllocFit.fixedArrayAllocFitStore, hPrevious, hg2]
    apply TradeAppendCopy.tradeCopyProg_spec env
      (TradeAllocFit.tradeAllocFitStore st choice) allocBase choice.node.root
      source g2 choice.node.capacity (UInt64.ofNat (ts.length + 1)) ts
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame] using hParams
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame,
        List.length_set] using hLocals
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame] using hValues
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hSourceLocal
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hTotalLocal
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hLengthLocal
    · simp [allocBase, TradeAllocSearch.tradeAllocSearchFrame, hLocals]
    · exact hTotalU
    · exact hTotal64
    · exact hTarget48
    · unfold fixedArrayBytes at hSource32
      omega
    · exact hTarget32
    · exact hTargetFit
    · exact hPayloadSep
    · exact hg2Fit
    · exact BookAllocFit.freshFixedArrayAt_fixedArrayAllocFitStore 4
        hList hTake
    · exact hOwnedFit.2
    · intro st1 hInv
      exact hFitDone choice hTake st1 hInv
  · intro previous
    let allocBase := TradeAllocSearch.tradeAllocSearchFrame base
      (tradeArrayBytesU (ts.length + 1)) previous 0
      (g0 + 48 + tradeArrayBytesU (ts.length + 1))
      ((g0 + 48 + tradeArrayBytesU (ts.length + 1) - 1) / 65536 + 1)
      (g0 + 48)
    have hTargetNat : (g0 + 48).toNat = g0.toNat + 48 := by
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48, Nat.mod_eq_of_lt (by omega)]
    have hTarget32 : (g0 + 48).toNat +
        ((ts.length + 1) * 4 + 1) * 8 < 4294967296 := by
      have hFit32Nat := hFit32
      rw [hNeedNat] at hFit32Nat
      unfold tradeArrayBytes fixedArrayBytes at hFit32Nat
      rw [hTargetNat]
      omega
    have hTargetFit : (g0 + 48).toNat +
        ((ts.length + 1) * 4 + 1) * 8 ≤
          (TradeAllocBump.tradeAllocBumpStore st g0
            (tradeArrayBytesU (ts.length + 1))).mem.pages * 65536 := by
      have hFitNat := hFit
      rw [hNeedNat] at hFitNat
      unfold tradeArrayBytes fixedArrayBytes at hFitNat
      change (g0 + 48).toNat + ((ts.length + 1) * 4 + 1) * 8 ≤
        st.mem.pages * 65536
      rw [hTargetNat]
      omega
    have hPayloadSep : flatWordsDisjoint
        (flatWordsRegion (g0 + 48) ((ts.length + 1) * 4))
        (flatWordsRegion source (ts.length * 4)) := by
      unfold flatWordsDisjoint flatWordsRegion
      right
      unfold fixedArrayBytes at hSourceCapacity
      omega
    have hOwnedBump : OwnedTradeArrayAt
        (TradeAllocBump.tradeAllocBumpStore st g0
          (tradeArrayBytesU (ts.length + 1))) source sourceCapacity ts :=
      ownedTradeArrayAt_fixedArrayAllocBumpStore hFit32 hSource48
        hSource32 hSourceCapacity hSourceBelow hOwned
    have hg2Bump :
        (TradeAllocBump.tradeAllocBumpStore st g0
          (tradeArrayBytesU (ts.length + 1))).globals.globals[2]? =
            some (.i64 g2) := by
      simp [TradeAllocBump.tradeAllocBumpStore,
        BookAllocBump.fixedArrayAllocBumpStore, hg2]
    apply TradeAppendCopy.tradeCopyProg_spec env
      (TradeAllocBump.tradeAllocBumpStore st g0
        (tradeArrayBytesU (ts.length + 1))) allocBase (g0 + 48) source g2
      (tradeArrayBytesU (ts.length + 1)) (UInt64.ofNat (ts.length + 1)) ts
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame] using hParams
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame,
        List.length_set] using hLocals
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame] using hValues
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hSourceLocal
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hTotalLocal
    · simpa [allocBase, TradeAllocSearch.tradeAllocSearchFrame,
        List.getElem?_set] using hLengthLocal
    · simp [allocBase, TradeAllocSearch.tradeAllocSearchFrame, hLocals]
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
        (tradeArrayBytesU (ts.length + 1)) 4 hNeed8 hFit32
    · exact hOwnedBump.2
    · intro st1 hInv
      exact hBumpDone previous st1 hInv

end Project.ClobMatchFuel.TradeAllocCopy
