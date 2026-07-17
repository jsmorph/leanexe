import Project.ClobLimit.InternalFullBookSuffix
import Project.ClobMatchFuel.AllocatorFrame

/-!
# Complete full-book update

This module composes the empty-list allocation and both erased-book copy
loops.  Its continuation receives owned source and replacement books, exact
allocator state, and the allocation-to-final memory frame.  The component
instruction proofs remain opaque at this boundary.
-/

namespace Project.ClobLimit.InternalFullBookUpdate

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalFullBookPrefix
  Project.ClobLimit.InternalFullBookSuffix
  Project.ClobMatchFuel.AllocatorFrame

abbrev fullBookAllocStore (st : Store Unit) (n : Nat) (g0 : UInt64) :
    Store Unit :=
  fixedArrayAllocBumpStore st g0 (fixedArrayBytesU n 5) 5

def fullBookUpdateProg : Wasm.Program :=
  InternalFullBookAlloc.fullBookAllocProg ++
    fullBookPrefixProg ++ fullBookSuffixProg

set_option Elab.async false in
theorem fullBookUpdateProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (source sourceCapacity g0 g2 capacity next : UInt64)
    (os : List OrderL) (i : Nat)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[45]? = some (.i64 source))
    (hPrefixLocal : base.locals[48]? =
      some (.i64 (UInt64.ofNat (i * 5))))
    (hSuffixLocal : base.locals[49]? =
      some (.i64 (UInt64.ofNat ((os.length - 1 - i) * 5))))
    (hLengthLocal : base.locals[50]? =
      some (.i64 (UInt64.ofNat (os.length - 1))))
    (hCapacityLocal : base.locals[58]? = some (.i64 capacity))
    (hNextLocal : base.locals[59]? = some (.i64 next))
    (hi : i < os.length)
    (hn : os.length - 1 < UInt64.size)
    (hOrderWords64 : os.length * 5 < UInt64.size)
    (hbytes : fixedArrayBytes (os.length - 1) 5 + 7 < UInt64.size)
    (hTop : (g0 + 48 + fixedArrayBytesU (os.length - 1) 5).toNat =
      g0.toNat + 48 + (fixedArrayBytesU (os.length - 1) 5).toNat)
    (hFit32 : g0.toNat + 48 +
      (fixedArrayBytesU (os.length - 1) 5).toNat < 4294967296)
    (hFit : g0.toNat + 48 +
      (fixedArrayBytesU (os.length - 1) 5).toNat ≤
        st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hSourceCapacity : fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ st1,
      OwnedOrderArrayAt st1 source sourceCapacity os →
      OwnedOrderArrayAt st1 (g0 + 48)
        (fixedArrayBytesU (os.length - 1) 5) (os.eraseIdx i) →
      MemEqOutsideFlatWords
        (fullBookAllocStore st (os.length - 1) g0) st1
        (g0 + 48) ((os.length - 1) * 5) →
      st1.mem.pages = st.mem.pages →
      st1.globals.globals =
        (fullBookAllocStore st (os.length - 1) g0).globals.globals.set 2
          (.i64 (g2 + 1)) →
      wp «module» rest Q st1
        (suffixResultFrame base
          (fixedArrayBytesU (os.length - 1) 5) 0 0
          (g0 + 48 + fixedArrayBytesU (os.length - 1) 5)
          ((g0 + 48 + fixedArrayBytesU (os.length - 1) 5 - 1) /
            65536 + 1)
          (g0 + 48) ((os.length - 1 - i) * 5)) env) :
    wp «module» (fullBookUpdateProg ++ rest) Q st base env := by
  let n := os.length - 1
  let need := fixedArrayBytesU n 5
  let target := g0 + 48
  let targetWords := n * 5
  let prefixWords := i * 5
  let suffixWords := (os.length - 1 - i) * 5
  have hNeedNat : need.toNat = fixedArrayBytes n 5 := by
    have hBytes : fixedArrayBytes n 5 + 7 < UInt64.size := by
      simpa [n] using hbytes
    exact fixedArrayBytesU_toNat n 5 hn (by decide) (by omega)
  have hNeed8 : 8 ≤ need.toNat := by
    rw [hNeedNat]
    unfold fixedArrayBytes
    omega
  have hTargetNat : target.toNat = g0.toNat + 48 := by
    unfold target
    rw [UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48, Nat.mod_eq_of_lt (by omega)]
  have hTarget48 : 48 ≤ target.toNat := by
    rw [hTargetNat]
    omega
  have hSourcePayload32 :
      source.toNat + (os.length * 5 + 1) * 8 < 4294967296 := by
    unfold fixedArrayBytes at hSource32
    omega
  have hTarget32 :
      target.toNat + (targetWords + 1) * 8 < 4294967296 := by
    have hTargetBytes : (targetWords + 1) * 8 = fixedArrayBytes n 5 := by
      unfold targetWords fixedArrayBytes
      omega
    rw [hTargetNat, hTargetBytes, ← hNeedNat]
    simpa [n] using hFit32
  have hTargetFit :
      target.toNat + (targetWords + 1) * 8 ≤
        (fullBookAllocStore st n g0).mem.pages * 65536 := by
    have hTargetBytes : (targetWords + 1) * 8 = fixedArrayBytes n 5 := by
      unfold targetWords fixedArrayBytes
      omega
    rw [hTargetNat, hTargetBytes, ← hNeedNat,
      Project.Clob.fixedArrayAllocBumpStore_pages]
    simpa [n] using hFit
  have hPayloadSep : flatWordsDisjoint
      (flatWordsRegion target targetWords)
      (flatWordsRegion source (os.length * 5)) := by
    unfold flatWordsDisjoint flatWordsRegion
    right
    rw [hTargetNat]
    unfold fixedArrayBytes at hSourceCapacity
    omega
  have hSourceRegionSep : regionsDisjoint
      (flatWordsRegion target targetWords)
      (fixedArrayRegion source sourceCapacity) := by
    unfold regionsDisjoint flatWordsRegion fixedArrayRegion
    right
    rw [hTargetNat]
    omega
  have hOwnedAlloc : OwnedOrderArrayAt
      (fullBookAllocStore st n g0) source sourceCapacity os :=
    ownedOrderArrayAt_fixedArrayAllocBumpStore hFit32 hSource48 hSource32
      hSourceCapacity hSourceBelow hOwned
  have hg2Alloc :
      (fullBookAllocStore st n g0).globals.globals[2]? = some (.i64 g2) :=
    Project.Clob.fixedArrayAllocBumpStore_global_of_ne_zero st g0 need 5 2
      (.i64 g2) (by decide) hg2
  have hFresh : FreshFixedArrayAt
      (fullBookAllocStore st n g0) target need 5 :=
    Project.Clob.fixedArrayAllocBumpStore_spec st g0 need 5 hNeed8 hFit32
  have hPrefixU : (UInt64.ofNat prefixWords).toNat = prefixWords :=
    toNat_ofNat_lt (by simp [prefixWords]; omega)
  have hSuffixU : (UInt64.ofNat suffixWords).toNat = suffixWords :=
    toNat_ofNat_lt (by simp [suffixWords]; omega)
  unfold fullBookUpdateProg
  rw [List.append_assoc, List.append_assoc]
  apply InternalFullBookAlloc.fullBookAllocProg_spec env st base n g0 capacity
    next hParams hLocals hValues
  · simpa [n] using hLengthLocal
  · exact hCapacityLocal
  · exact hNextLocal
  · exact hn
  · simpa [n] using hbytes
  · simpa [n, need] using hTop
  · simpa [n, need] using hFit32
  · simpa [n, need] using hFit
  · exact hPages
  · exact hg0
  · exact hg1
  · apply fullBookPrefixProg_spec env (fullBookAllocStore st n g0) base need
      0 0 (g0 + 48 + need) ((g0 + 48 + need - 1) / 65536 + 1)
      target source g2 need (UInt64.ofNat n) os targetWords prefixWords
    · exact hParams
    · exact hLocals
    · exact hValues
    · exact hSourceLocal
    · simpa [prefixWords] using hPrefixLocal
    · simpa [n] using hLengthLocal
    · exact hPrefixU
    · simp [prefixWords]
      omega
    · simp [prefixWords, targetWords, n]
      omega
    · simp [prefixWords]
      omega
    · exact hTarget48
    · exact hSourcePayload32
    · exact hTarget32
    · exact hTargetFit
    · exact hPayloadSep
    · exact hg2Alloc
    · exact hFresh
    · exact hOwnedAlloc.2
    · intro st1 hPrefixInv hPrefix
      obtain ⟨_, _, _, hCopyPages, hCopyGlobals, hFresh1, hLength1,
        hOrders1, hOutside1, _⟩ := hPrefixInv
      apply fullBookSuffixProg_spec env (fullBookAllocStore st n g0) st1 base
        need 0 0 (g0 + 48 + need)
        ((g0 + 48 + need - 1) / 65536 + 1) target source g2 need
        (UInt64.ofNat n) os i targetWords prefixWords suffixWords
      · exact hParams
      · exact hLocals
      · exact hSourceLocal
      · simpa [prefixWords] using hPrefixLocal
      · simpa [suffixWords] using hSuffixLocal
      · exact hPrefixU
      · exact hSuffixU
      · simp [suffixWords]
        omega
      · exact hi
      · rfl
      · simp [suffixWords]
      · rfl
      · rfl
      · exact hTarget48
      · exact hSourcePayload32
      · exact hTarget32
      · exact hTargetFit
      · exact hPayloadSep
      · exact hCopyPages
      · exact hCopyGlobals
      · exact hFresh1
      · exact hLength1
      · exact hOwnedAlloc.2
      · exact hOrders1
      · exact hOutside1
      · exact hPrefix
      · intro st2 hSuffixInv hTargetOrders
        obtain ⟨_, _, _, hFinalPagesAlloc, hFinalGlobals, hFreshFinal, _, _,
          hOutsideFinal, _, _⟩ := hSuffixInv
        have hFinalPages : st2.mem.pages = st.mem.pages :=
          hFinalPagesAlloc.trans
            (Project.Clob.fixedArrayAllocBumpStore_pages st g0 need 5)
        have hSourceFinal : OwnedOrderArrayAt st2 source sourceCapacity os :=
          OwnedOrderArrayAt.frame_outsideFlatWords hSource48 hSource32
            hSourceCapacity hFinalPagesAlloc hSourceRegionSep hOutsideFinal
            hOwnedAlloc
        simpa [n, need, target, targetWords, suffixWords] using
          hDone st2 hSourceFinal ⟨hFreshFinal, hTargetOrders⟩ hOutsideFinal
            hFinalPages hFinalGlobals

end Project.ClobLimit.InternalFullBookUpdate
