import Project.ClobMatchFuel.BookAlloc
import Project.ClobMatchFuel.AllocatorFrame
import Project.ClobMatchFuel.BookEraseSuffix

/-!
# Full-fill book allocation and erasure

This module first composes the two generated copy loops that erase a matched
order.  The allocator composition then supplies either a reused free node or a
new heap object to that common copy theorem.
-/

namespace Project.ClobMatchFuel.BookAllocErase

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def bookCopiesProg : Wasm.Program :=
  BookErasePrefix.erasePrefixProg ++ BookEraseSuffix.eraseSuffixProg

set_option Elab.async false in
theorem bookCopiesProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (need previous current capacity next target source g2 arrayCapacity
      newLength : UInt64)
    (os : List OrderL) (i targetWords prefixWords suffixWords : Nat)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[57]? = some (.i64 source))
    (hPrefixLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat prefixWords)))
    (hSuffixLocal : base.locals[61]? =
      some (.i64 (UInt64.ofNat suffixWords)))
    (hLengthLocal : base.locals[62]? = some (.i64 newLength))
    (hPrefixU : (UInt64.ofNat prefixWords).toNat = prefixWords)
    (hSuffixU : (UInt64.ofNat suffixWords).toNat = suffixWords)
    (hPrefix64 : prefixWords < UInt64.size)
    (hSuffix64 : suffixWords < UInt64.size)
    (hi : i < os.length)
    (hPrefixWords : prefixWords = i * 5)
    (hSuffixWords : suffixWords = (os.length - 1 - i) * 5)
    (hTargetWords : targetWords = (os.length - 1) * 5)
    (hNewLength : newLength = UInt64.ofNat (os.length - 1))
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 : source.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + (targetWords + 1) * 8 < 4294967296)
    (hTargetFit : target.toNat + (targetWords + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint (flatWordsRegion target targetWords)
      (flatWordsRegion source (os.length * 5)))
    (hg2 : st0.globals.globals[2]? = some (.i64 g2))
    (hFresh : FreshOrderArrayAt st0 target arrayCapacity)
    (hOrders : OrdersAt st0 source os)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st2,
      BookEraseSuffix.eraseSuffixInv st0 base need previous current capacity
          next target source g2 arrayCapacity newLength os targetWords
          prefixWords suffixWords st2
          (BookErasePrefix.eraseCopyFrame base need previous current capacity
            next target suffixWords) →
        OrdersAt st2 target (os.eraseIdx i) →
        wp «module» rest Q st2
          (BookEraseSuffix.eraseResultFrame base need previous current capacity
            next target suffixWords) env) :
    wp «module» (bookCopiesProg ++ rest) Q st0
      (BookAllocSearch.bookAllocSearchFrame base need previous current capacity
        next target) env := by
  unfold bookCopiesProg
  rw [List.append_assoc]
  apply BookErasePrefix.erasePrefixProg_spec env st0 base need previous current
    capacity next target source g2 arrayCapacity newLength os targetWords
    prefixWords hParams hLocals hValues hSourceLocal hPrefixLocal hLengthLocal
    hPrefixU hPrefix64 (by rw [hPrefixWords, hTargetWords]; omega)
    (by rw [hPrefixWords]; omega) hTarget48 hSource32 hTarget32 hTargetFit
    hsep hg2 hFresh hOrders Q (BookEraseSuffix.eraseSuffixProg ++ rest)
  intro st1 hPrefixInv hPrefix
  obtain ⟨_, _, _, hPages, hGlobals, hFresh1, hLength, hOrders1,
    hOutside, _⟩ := hPrefixInv
  apply BookEraseSuffix.eraseSuffixProg_spec env st0 st1 base need previous
    current capacity next target source g2 arrayCapacity newLength os i
    targetWords prefixWords suffixWords hParams hLocals hSourceLocal
    hPrefixLocal hSuffixLocal hPrefixU hSuffixU hSuffix64 hi hPrefixWords
    hSuffixWords hTargetWords hNewLength hTarget48 hSource32 hTarget32
    hTargetFit hsep hPages hGlobals hFresh1 hLength hOrders hOrders1
    hOutside hPrefix Q rest
  intro st2 hSuffixInv hTargetOrders
  exact hDone st2 hSuffixInv hTargetOrders

def bookAllocEraseProg : Wasm.Program :=
  BookAlloc.bookAllocProg ++ bookCopiesProg

set_option Elab.async false in
theorem bookAllocEraseProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (source sourceCapacity g0 g2 capacity next : UInt64)
    (os : List OrderL) (i : Nat) (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[57]? = some (.i64 source))
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
      takeFirstFitFrom 0 (orderArrayBytesU (os.length - 1)) nodes =
          some choice →
      ∀ st2,
        BookEraseSuffix.eraseSuffixInv
            (BookAllocFit.bookAllocFitStore st choice) base
            (orderArrayBytesU (os.length - 1)) choice.previous
            choice.node.root choice.node.capacity choice.next choice.node.root
            source g2 choice.node.capacity (UInt64.ofNat (os.length - 1)) os
            ((os.length - 1) * 5) (i * 5)
            ((os.length - 1 - i) * 5) st2
            (BookErasePrefix.eraseCopyFrame base
              (orderArrayBytesU (os.length - 1)) choice.previous
              choice.node.root choice.node.capacity choice.next
              choice.node.root ((os.length - 1 - i) * 5)) →
        OrdersAt st2 choice.node.root (os.eraseIdx i) →
        wp «module» rest Q st2
          (BookEraseSuffix.eraseResultFrame base
            (orderArrayBytesU (os.length - 1)) choice.previous
            choice.node.root choice.node.capacity choice.next choice.node.root
            ((os.length - 1 - i) * 5)) env)
    (hBumpDone : ∀ previous : UInt64, ∀ st2,
      BookEraseSuffix.eraseSuffixInv
          (BookAllocBump.bookAllocBumpStore st g0
            (orderArrayBytesU (os.length - 1))) base
          (orderArrayBytesU (os.length - 1)) previous 0
          (g0 + 48 + orderArrayBytesU (os.length - 1))
          ((g0 + 48 + orderArrayBytesU (os.length - 1) - 1) / 65536 + 1)
          (g0 + 48) source g2 (orderArrayBytesU (os.length - 1))
          (UInt64.ofNat (os.length - 1)) os ((os.length - 1) * 5)
          (i * 5) ((os.length - 1 - i) * 5) st2
          (BookErasePrefix.eraseCopyFrame base
            (orderArrayBytesU (os.length - 1)) previous 0
            (g0 + 48 + orderArrayBytesU (os.length - 1))
            ((g0 + 48 + orderArrayBytesU (os.length - 1) - 1) /
              65536 + 1)
            (g0 + 48) ((os.length - 1 - i) * 5)) →
      OrdersAt st2 (g0 + 48) (os.eraseIdx i) →
      wp «module» rest Q st2
        (BookEraseSuffix.eraseResultFrame base
          (orderArrayBytesU (os.length - 1)) previous 0
          (g0 + 48 + orderArrayBytesU (os.length - 1))
          ((g0 + 48 + orderArrayBytesU (os.length - 1) - 1) / 65536 + 1)
          (g0 + 48) ((os.length - 1 - i) * 5)) env) :
    wp «module» (bookAllocEraseProg ++ rest) Q st base env := by
  have hNeedNat : (orderArrayBytesU (os.length - 1)).toNat =
      orderArrayBytes (os.length - 1) := by
    exact fixedArrayBytesU_toNat (os.length - 1) 5 hn (by decide) (by
      change fixedArrayBytes (os.length - 1) 5 + 7 < UInt64.size at hbytes
      omega)
  have hPrefixU : (UInt64.ofNat (i * 5)).toNat = i * 5 :=
    toNat_ofNat_lt (by omega)
  have hSuffixU :
      (UInt64.ofNat ((os.length - 1 - i) * 5)).toNat =
        (os.length - 1 - i) * 5 :=
    toNat_ofNat_lt (by omega)
  have hNeed8 : 8 ≤ (orderArrayBytesU (os.length - 1)).toNat := by
    rw [hNeedNat]
    unfold orderArrayBytes fixedArrayBytes
    omega
  unfold bookAllocEraseProg
  rw [List.append_assoc]
  apply BookAlloc.bookAllocProg_spec env st base (os.length - 1) g0 capacity
    next nodes hParams hLocals hValues hLengthLocal hCapacityLocal hNextLocal
    hn hbytes htop hFit32 hFit hPages hg0 hg1 hList Q
    (bookCopiesProg ++ rest)
  · intro choice hTake
    have hChoiceMem : choice.node ∈ nodes :=
      takeFirstFitFrom_some_mem hTake
    obtain ⟨hTarget48, hTarget32Full, hTargetFitFull⟩ :=
      hList.mem_bounds hChoiceMem
    have hChoiceCapacity := takeFirstFitFrom_some_capacity hTake
    rw [UInt64.le_iff_toNat_le, hNeedNat] at hChoiceCapacity
    have hTarget32 : choice.node.root.toNat +
        ((os.length - 1) * 5 + 1) * 8 < 4294967296 := by
      unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hFitPages : (BookAllocFit.bookAllocFitStore st choice).mem.pages =
        st.mem.pages := by
      simp only [BookAllocFit.bookAllocFitStore,
        BookAllocFit.fixedArrayAllocFitStore,
        BookAllocFit.fixedArrayAllocFitMem, unlinkFreeChoice,
        Mem.write64_pages]
      split <;> rfl
    have hTargetFit : choice.node.root.toNat +
        ((os.length - 1) * 5 + 1) * 8 ≤
          (BookAllocFit.bookAllocFitStore st choice).mem.pages * 65536 := by
      rw [hFitPages]
      unfold orderArrayBytes fixedArrayBytes at hChoiceCapacity
      omega
    have hPayloadSep : flatWordsDisjoint
        (flatWordsRegion choice.node.root ((os.length - 1) * 5))
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
        (BookAllocFit.bookAllocFitStore st choice) source sourceCapacity os :=
      ownedOrderArrayAt_fixedArrayAllocFitStore hList hTake hSource48
        hSource32 hSourceCapacity hSourceFree hOwned
    have hg2Fit :
        (BookAllocFit.bookAllocFitStore st choice).globals.globals[2]? =
          some (.i64 g2) := by
      by_cases hPrevious : choice.previous = 0
      · simp only [BookAllocFit.bookAllocFitStore,
          BookAllocFit.fixedArrayAllocFitStore, hPrevious, if_pos]
        simpa [List.getElem?_set] using hg2
      · simp [BookAllocFit.bookAllocFitStore,
          BookAllocFit.fixedArrayAllocFitStore, hPrevious, hg2]
    apply bookCopiesProg_spec env (BookAllocFit.bookAllocFitStore st choice)
      base (orderArrayBytesU (os.length - 1)) choice.previous
      choice.node.root choice.node.capacity choice.next choice.node.root source
      g2 choice.node.capacity (UInt64.ofNat (os.length - 1)) os i
      ((os.length - 1) * 5) (i * 5) ((os.length - 1 - i) * 5) hParams
      hLocals hValues hSourceLocal hPrefixLocal hSuffixLocal hLengthLocal
      hPrefixU hSuffixU (by omega) (by omega) hi rfl rfl rfl rfl hTarget48
      (by unfold fixedArrayBytes at hSource32; omega) hTarget32 hTargetFit
      hPayloadSep hg2Fit
      (BookAllocFit.freshFixedArrayAt_fixedArrayAllocFitStore 5 hList hTake)
      hOwnedFit.2 Q rest
    intro st2 hSuffixInv hTargetOrders
    exact hFitDone choice hTake st2 hSuffixInv hTargetOrders
  · intro previous
    have hTargetNat : (g0 + 48).toNat = g0.toNat + 48 := by
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48, Nat.mod_eq_of_lt (by omega)]
    have hTarget32 : (g0 + 48).toNat +
        ((os.length - 1) * 5 + 1) * 8 < 4294967296 := by
      have hFit32Nat := hFit32
      rw [hNeedNat] at hFit32Nat
      unfold orderArrayBytes fixedArrayBytes at hFit32Nat
      rw [hTargetNat]
      omega
    have hTargetFit : (g0 + 48).toNat +
        ((os.length - 1) * 5 + 1) * 8 ≤
          (BookAllocBump.bookAllocBumpStore st g0
            (orderArrayBytesU (os.length - 1))).mem.pages * 65536 := by
      have hFitNat := hFit
      rw [hNeedNat] at hFitNat
      unfold orderArrayBytes fixedArrayBytes at hFitNat
      change (g0 + 48).toNat + ((os.length - 1) * 5 + 1) * 8 ≤
        st.mem.pages * 65536
      rw [hTargetNat]
      omega
    have hPayloadSep : flatWordsDisjoint
        (flatWordsRegion (g0 + 48) ((os.length - 1) * 5))
        (flatWordsRegion source (os.length * 5)) := by
      unfold flatWordsDisjoint flatWordsRegion
      right
      unfold fixedArrayBytes at hSourceCapacity
      omega
    have hOwnedBump : OwnedOrderArrayAt
        (BookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU (os.length - 1))) source sourceCapacity os :=
      ownedOrderArrayAt_fixedArrayAllocBumpStore hFit32 hSource48 hSource32
        hSourceCapacity hSourceBelow hOwned
    have hg2Bump :
        (BookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU (os.length - 1))).globals.globals[2]? =
            some (.i64 g2) := by
      simp [BookAllocBump.bookAllocBumpStore,
        BookAllocBump.fixedArrayAllocBumpStore, hg2]
    apply bookCopiesProg_spec env
      (BookAllocBump.bookAllocBumpStore st g0
        (orderArrayBytesU (os.length - 1))) base
      (orderArrayBytesU (os.length - 1)) previous 0
      (g0 + 48 + orderArrayBytesU (os.length - 1))
      ((g0 + 48 + orderArrayBytesU (os.length - 1) - 1) / 65536 + 1)
      (g0 + 48) source g2 (orderArrayBytesU (os.length - 1))
      (UInt64.ofNat (os.length - 1)) os i ((os.length - 1) * 5) (i * 5)
      ((os.length - 1 - i) * 5) hParams hLocals hValues hSourceLocal
      hPrefixLocal hSuffixLocal hLengthLocal hPrefixU hSuffixU (by omega)
      (by omega) hi rfl rfl rfl rfl (by rw [hTargetNat]; omega)
      (by unfold fixedArrayBytes at hSource32; omega) hTarget32 hTargetFit
      hPayloadSep hg2Bump
      (BookAllocBump.freshFixedArrayAt_fixedArrayAllocBumpStore st g0
        (orderArrayBytesU (os.length - 1)) 5 hNeed8 hFit32)
      hOwnedBump.2 Q rest
    intro st2 hSuffixInv hTargetOrders
    exact hBumpDone previous st2 hSuffixInv hTargetOrders

end Project.ClobMatchFuel.BookAllocErase
