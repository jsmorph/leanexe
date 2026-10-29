import LeanExe.Pipeline.AlignedFreeList
import LeanExe.ProofKit.ReleaseTree

/-!
`release` on a tree of records under `wpA`: the ports of `wp_loop_ghost`, `dropReference_spec`,
`dropSlot_spec`, `slotLoop_spec`, `dropChildren_spec`, and `release_tree_run_top`.  The pending
loop reads each record's header words at its pointer minus 48, 40, 24, 16, and 8, and its slots
at its pointer plus 8 times the slot's index, and links each child through the child's count
word, at the child's pointer minus 40.  Every access is aligned when the blocks of the tree start
at multiples of 8, so that every record pointer and child pointer is a multiple of 8.  The loop's
invariant adds to `Releasing` that the heap is aligned and that the blocks of the pending records
start and end at multiples of 8.  `Releasing.startBlocks` gives the second fact at the loop's
entry.  `Releasing.nextBlocks` keeps it across a step, since the blocks of the new pending records
are blocks of the old, and the capacity of the freed record, a multiple of 8, keeps the heap
aligned through `Heap.Aligned.release`.
-/

namespace LeanExe.Pipeline

open Wasm LeanExe.Runtime LeanExe.ProofKit

attribute [-simp] Wasm.Mem.read64_write64_same
attribute [local simp] Memory.read64_write64

theorem wpA_loop_ghost {α : Type} {m : Module} {env : HostEnv α} {ps rs : Nat}
    {body rest : Program} {Q : Assertion α} {st : Store α} {s : Locals}
    (Inv : Nat → AssertionF α) (n : Nat) (hInit : Inv n st s)
    (hStep : ∀ n st s, Inv n st s →
        wpA m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wpA m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s' =>
              ∃ n' < n, Inv n' st' { s' with values := s'.values.take ps ++ s.values.drop ps }
            | .Break (k+1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st s env) :
    wpA m (.loop ps rs body :: rest) Q st s env := by
  classical
  refine wpA_loop_cons (fun st s => ∃ n, Inv n st s)
    (fun st s => if h : ∃ n, Inv n st s then Nat.find h else 0) ⟨n, hInit⟩ ?_
  intro st s hEx
  refine wpA.conseq ?_ (hStep _ st s (Nat.find_spec hEx))
  intro c hc
  rcases c with ⟨st', s'⟩ | ⟨_ | k, st', s'⟩ | _ | _ | _ | _ | _ | _
  · exact hc
  · obtain ⟨n', hlt, hInv⟩ := hc
    refine ⟨⟨n', hInv⟩, ?_⟩
    rw [dite_eq_left_of_eq_true (eq_true ⟨n', hInv⟩), dite_eq_left_of_eq_true (eq_true hEx)]
    exact lt_of_le_of_lt (Nat.find_min' _ hInv) hlt
  all_goals exact hc

theorem dropReference_specA {m : Module} (env : HostEnv Unit) (store : Store Unit)
    (v : ReleaseVars) (hBase : 48 ≤ v.child.toNat) (hFit : v.child.toNat < 4294967296)
    (hMemory : v.child.toNat ≤ store.mem.pages * 65536)
    (hMagic : store.mem.read64 (UInt32.ofNat (v.child.toNat - 48)) = magic)
    (hCount : store.mem.read64 (UInt32.ofNat (v.child.toNat - 40)) = 1)
    (hAl : v.child.toNat % 8 = 0)
    (Q : Assertion Unit) (after : Program)
    (hNext : wpA m after Q
      { store with mem := store.mem.write64 (UInt32.ofNat (v.child.toNat - 40)) v.pending }
      v.link.toLocals env) :
    wpA m (dropReference releaseChild releaseCount releasePending ++ after) Q store
      v.toLocals env := by
  obtain ⟨root, count, pending, object, kind, length, width, mask, element, slot, ptr, previous,
    current⟩ := v
  simp only [ReleaseVars.link] at hNext hBase hFit hMemory hMagic hCount hAl ⊢
  have hSub : ∀ k : UInt64, k.toNat ≤ 48 → (ptr - k).toNat = ptr.toNat - k.toNat := fun k hk =>
    UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)
  have hs48 : (ptr - 48).toNat = ptr.toNat - 48 := hSub 48 (by decide)
  have hs40 : (ptr - 40).toNat = ptr.toNat - 40 := hSub 40 (by decide)
  have hm48 : (ptr.toNat - 48) % 4294967296 = ptr.toNat - 48 := Nat.mod_eq_of_lt (by omega)
  have hm40 : (ptr.toNat - 40) % 4294967296 = ptr.toNat - 40 := Nat.mod_eq_of_lt (by omega)
  have hb48 : ptr.toNat - 48 + 8 ≤ store.mem.pages * 65536 := by omega
  have hb40 : ptr.toNat - 40 + 8 ≤ store.mem.pages * 65536 := by omega
  have hc48 : ¬ store.mem.pages * 65536 < ptr.toNat - 48 + 8 := by omega
  have hc40 : ¬ store.mem.pages * 65536 < ptr.toNat - 40 + 8 := by omega
  have hpa48 : (ptr.toNat - 48) % 8 = 0 := by omega
  have hpa40 : (ptr.toNat - 40) % 8 = 0 := by omega
  simp [dropReference, checkMagic, headerLoad, headerStore, ReleaseVars.toLocals, releaseChild,
    releaseCount, releasePending, wpA_simp, wp_simp, hs48, hm48, hc48, hpa48, hMagic]
  refine wpA_iff_cons rfl ?_
  simp [wpA_simp, wp_simp, hs40, hm40, hc40, hpa40, hCount]
  refine wpA_iff_cons rfl ?_
  simp [wpA_simp, wp_simp, hs40, hm40, hc40, hpa40]
  exact hNext

theorem dropSlot_specA {m : Module} (env : HostEnv Unit) (store : Store Unit) (v : ReleaseVars)
    (slots : List Slot) (i : Nat) (hi : i < slots.length) (hShort : slots.length ≤ 64)
    (hMask : v.mask = maskOf slots) (hSlotLocal : v.slot = UInt64.ofNat i)
    (hAddress : v.object.toNat + 8 * slots.length < 4294967296)
    (hMemory : v.object.toNat + 8 * slots.length ≤ store.mem.pages * 65536)
    (hNull : slots[i].bit = 1 → childRecords store.mem v.object i [slots[i]] = [] →
      store.mem.read64 (slotAddress v.object i) = 0)
    (hKid : ∀ k ∈ childRecords store.mem v.object i [slots[i]], ChildHeader store k.1)
    (hObjectAl : v.object.toNat % 8 = 0)
    (hKidAl : ∀ k ∈ childRecords store.mem v.object i [slots[i]], k.1.toNat % 8 = 0)
    (Q : Assertion Unit) (after : Program)
    (hNext : ∀ count child, wpA m after Q
      { store with mem := (linkChildren store.mem v.pending
        (childRecords store.mem v.object i [slots[i]])).1 }
      (v.afterSlot count child (linkChildren store.mem v.pending
        (childRecords store.mem v.object i [slots[i]])).2).toLocals env) :
    wpA m (dropSlot ++ after) Q store v.toLocals env := by
  obtain ⟨root, count, pending, q, kind, length, width, mask, element, slot, child, previous,
    current⟩ := v
  simp only at hMask hSlotLocal hAddress hMemory hNull hKid hObjectAl hKidAl hNext ⊢
  subst hMask hSlotLocal
  have hTest := maskOf_test slots hShort i hi
  have hSlotAt : (slotAddress q i).toNat = q.toNat + 8 * i := slotAddress_toNat (by omega)
  have hLoad : (q + UInt64.ofNat i * 8).toUInt32 = slotAddress q i := by
    simp only [slotAddress]
    congr 2
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mul, UInt64.toNat_ofNat']
    have : (8 : UInt64).toNat = 8 := rfl
    rw [this]
    omega
  simp [dropSlot, dropMaskedSlot, ReleaseVars.toLocals, releaseMask, releaseSlot, releaseChild,
    releaseCount, releasePending, releaseObject, wpA_simp, wp_simp, hTest]
  generalize hs : slots[i] = s at hNull hKid hKidAl hNext
  cases s with
  | word w =>
    simp [Slot.bit]
    refine wpA_iff_cons rfl ?_
    simp [wpA_simp, wp_simp]
    simpa [childRecords, linkChildren, ReleaseVars.afterSlot, ReleaseVars.toLocals] using
      hNext count child
  | child n =>
    have hmod : (q.toNat + i * 8) % 4294967296 = q.toNat + i * 8 := Nat.mod_eq_of_lt (by omega)
    have hAddrEq : UInt32.ofNat (q.toNat + i * 8) = slotAddress q i :=
      UInt32.toNat_inj.mp (by rw [hSlotAt, UInt32.toNat_ofNat']; omega)
    simp [Slot.bit]
    refine wpA_iff_cons rfl ?_
    have hb2 : ¬ store.mem.pages * 65536 < (slotAddress q i).toNat + 8 := by omega
    have hsa : (slotAddress q i).toNat % 8 = 0 := by omega
    simp [wpA_simp, wp_simp, hmod, hAddrEq, hb2, hsa]
    cases n with
    | null =>
      simp [hNull (by simp [Slot.bit]) (by simp [childRecords])]
      refine wpA_iff_cons rfl ?_
      simp [wpA_simp, wp_simp]
      simpa [childRecords, linkChildren, ReleaseVars.afterSlot, ReleaseVars.toLocals] using
        hNext count 0
    | record cs =>
      have hc := hKid _ (List.mem_singleton_self (store.mem.read64 (slotAddress q i), cs))
      have hcAl := hKidAl _ (List.mem_singleton_self (store.mem.read64 (slotAddress q i), cs))
      have hNe : store.mem.read64 (slotAddress q i) ≠ 0 := by
        intro h
        have := hc.base
        simp only at this
        rw [h] at this
        simp at this
      simp [hNe]
      refine wpA_iff_cons rfl ?_
      rw [show (if ¬(1 : UInt32) = 0 then dropReference 10 1 2 else []) = dropReference 10 1 2
        from rfl, ← List.append_nil (dropReference 10 1 2)]
      refine dropReference_specA env store
        ⟨root, count, pending, q, kind, length, width, maskOf slots, element, UInt64.ofNat i,
          store.mem.read64 (slotAddress q i), previous, current⟩ hc.base hc.address hc.memory
        hc.magic hc.count hcAl _ _ ?_
      simp [wpA_simp, wp_simp]
      simpa [childRecords, linkChildren, ReleaseVars.afterSlot, ReleaseVars.link,
        ReleaseVars.toLocals] using hNext 1 (store.mem.read64 (slotAddress q i))
  | array ws =>
    have hmod : (q.toNat + i * 8) % 4294967296 = q.toNat + i * 8 := Nat.mod_eq_of_lt (by omega)
    have hAddrEq : UInt32.ofNat (q.toNat + i * 8) = slotAddress q i :=
      UInt32.toNat_inj.mp (by rw [hSlotAt, UInt32.toNat_ofNat']; omega)
    simp [Slot.bit]
    refine wpA_iff_cons rfl ?_
    have hb2 : ¬ store.mem.pages * 65536 < (slotAddress q i).toNat + 8 := by omega
    have hsa : (slotAddress q i).toNat % 8 = 0 := by omega
    simp [wpA_simp, wp_simp, hmod, hAddrEq, hb2, hsa]
    have hc := hKid _ (List.mem_singleton_self (store.mem.read64 (slotAddress q i), []))
    have hcAl := hKidAl _ (List.mem_singleton_self (store.mem.read64 (slotAddress q i), []))
    have hNe : store.mem.read64 (slotAddress q i) ≠ 0 := by
      intro h
      have := hc.base
      simp only at this
      rw [h] at this
      simp at this
    simp [hNe]
    refine wpA_iff_cons rfl ?_
    rw [show (if ¬(1 : UInt32) = 0 then dropReference 10 1 2 else []) = dropReference 10 1 2
      from rfl, ← List.append_nil (dropReference 10 1 2)]
    refine dropReference_specA env store
      ⟨root, count, pending, q, kind, length, width, maskOf slots, element, UInt64.ofNat i,
        store.mem.read64 (slotAddress q i), previous, current⟩ hc.base hc.address hc.memory
      hc.magic hc.count hcAl _ _ ?_
    simp [wpA_simp, wp_simp]
    simpa [childRecords, linkChildren, ReleaseVars.afterSlot, ReleaseVars.link,
      ReleaseVars.toLocals] using hNext 1 (store.mem.read64 (slotAddress q i))
  | bytes data =>
    have hmod : (q.toNat + i * 8) % 4294967296 = q.toNat + i * 8 := Nat.mod_eq_of_lt (by omega)
    have hAddrEq : UInt32.ofNat (q.toNat + i * 8) = slotAddress q i :=
      UInt32.toNat_inj.mp (by rw [hSlotAt, UInt32.toNat_ofNat']; omega)
    simp [Slot.bit]
    refine wpA_iff_cons rfl ?_
    have hb2 : ¬ store.mem.pages * 65536 < (slotAddress q i).toNat + 8 := by omega
    have hsa : (slotAddress q i).toNat % 8 = 0 := by omega
    simp [wpA_simp, wp_simp, hmod, hAddrEq, hb2, hsa]
    by_cases hEmpty : data.data.size = 0
    · simp [hNull (by simp [Slot.bit]) (by simp [childRecords, bufferRoots, hEmpty])]
      refine wpA_iff_cons rfl ?_
      simp [wpA_simp, wp_simp]
      simpa [childRecords, bufferRoots, hEmpty, linkChildren, ReleaseVars.afterSlot,
        ReleaseVars.toLocals] using hNext count 0
    · have hk : (store.mem.read64 (slotAddress q i), ([] : List Slot)) ∈
          childRecords store.mem q i [.bytes data] := by
        simp [childRecords, bufferRoots, hEmpty]
      have hc := hKid _ hk
      have hcAl := hKidAl _ hk
      have hNe : store.mem.read64 (slotAddress q i) ≠ 0 := by
        intro h
        have := hc.base
        simp only at this
        rw [h] at this
        simp at this
      simp [hNe]
      refine wpA_iff_cons rfl ?_
      rw [show (if ¬(1 : UInt32) = 0 then dropReference 10 1 2 else []) = dropReference 10 1 2
        from rfl, ← List.append_nil (dropReference 10 1 2)]
      refine dropReference_specA env store
        ⟨root, count, pending, q, kind, length, width, maskOf slots, element, UInt64.ofNat i,
          store.mem.read64 (slotAddress q i), previous, current⟩ hc.base hc.address hc.memory
        hc.magic hc.count hcAl _ _ ?_
      simp [wpA_simp, wp_simp]
      simpa [childRecords, bufferRoots, hEmpty, linkChildren, ReleaseVars.afterSlot,
        ReleaseVars.link, ReleaseVars.toLocals] using hNext 1 (store.mem.read64 (slotAddress q i))

theorem slotLoop_specA {m : Module} (env : HostEnv Unit) (store : Store Unit) (v : ReleaseVars)
    (slots : List Slot) (hShort : slots.length ≤ 64)
    (hMask : v.mask = maskOf slots) (hWidth : v.width = UInt64.ofNat slots.length)
    (hAddress : v.object.toNat + 8 * slots.length < 4294967296)
    (hMemory : v.object.toNat + 8 * slots.length ≤ store.mem.pages * 65536)
    (hNull : ∀ i (h : i < slots.length), slots[i].bit = 1 →
      childRecords store.mem v.object i [slots[i]] = [] →
      store.mem.read64 (slotAddress v.object i) = 0)
    (hKids : ∀ k ∈ childRecords store.mem v.object 0 slots, ChildHeader store k.1)
    (hApart : ((childRecords store.mem v.object 0 slots).map fun k => (k.1.toNat - 48, 48)).Pairwise
      regionsDisjoint)
    (hPayload : ∀ k ∈ childRecords store.mem v.object 0 slots,
      regionsDisjoint (k.1.toNat - 48, 48) (v.object.toNat, 8 * slots.length))
    (hObjectAl : v.object.toNat % 8 = 0)
    (hKidsAl : ∀ k ∈ childRecords store.mem v.object 0 slots, k.1.toNat % 8 = 0)
    (Q : Assertion Unit) (after : Program)
    (hNext : ∀ v' : ReleaseVars, v'.root = v.root → v'.object = v.object → v'.kind = v.kind →
      v'.pending = (linkChildren store.mem v.pending (childRecords store.mem v.object 0 slots)).2 →
      wpA m after Q { store with mem := (linkChildren store.mem v.pending
        (childRecords store.mem v.object 0 slots)).1 } v'.toLocals env) :
    wpA m (countedLoop releaseSlot releaseWidth dropSlot ++ after) Q store v.toLocals env := by
  obtain ⟨root, count, pending, q, kind, length, width, mask, element, slot, child, previous,
    current⟩ := v
  simp only at hMask hWidth hAddress hMemory hNull hKids hApart hPayload hObjectAl hKidsAl hNext ⊢
  subst hMask hWidth
  simp [countedLoop, ReleaseVars.toLocals, releaseSlot, releaseWidth, wpA_simp, wp_simp]
  apply wpA_block_cons
  refine wpA_loop_cons (fun st s => ∃ i, i ≤ slots.length ∧
      st = { store with mem := (linkChildren store.mem pending
        (childRecords store.mem q 0 (slots.take i))).1 } ∧
      ∃ c ch, s = ReleaseVars.toLocals ⟨root, c, (linkChildren store.mem pending
        (childRecords store.mem q 0 (slots.take i))).2, q, kind, length,
        UInt64.ofNat slots.length, maskOf slots, element, UInt64.ofNat i, ch, previous, current⟩)
    (fun _ s => match s.get releaseSlot with
      | some (.i64 k) => slots.length - k.toNat
      | _ => 0)
    ⟨0, Nat.zero_le _, by simp [childRecords, linkChildren], count, child, by
      simp [ReleaseVars.toLocals, childRecords, linkChildren]⟩ ?_
  rintro st s ⟨i, hi, rfl, c, ch, rfl⟩
  have hLe : UInt64.ofNat slots.length ≤ UInt64.ofNat i ↔ slots.length ≤ i := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  simp [ReleaseVars.toLocals, wpA_simp, wp_simp]
  rcases Nat.lt_or_ge i slots.length with hLt | hGe
  · have hNot : ¬ UInt64.ofNat slots.length ≤ UInt64.ofNat i := fun h => by
      have := hLe.mp h
      omega
    simp only [hNot, ite_false]
    have hSplit := childRecords_split store.mem q slots i hLt
    have hSlotAt : (slotAddress q i).toNat = q.toNat + 8 * i := slotAddress_toNat (by omega)
    have hKids' : ∀ k ∈ childRecords store.mem q 0 slots, 48 ≤ k.1.toNat ∧
        k.1.toNat < 4294967296 ∧ (q.toNat + 8 * slots.length ≤ k.1.toNat - 48 ∨
          k.1.toNat ≤ q.toNat) := fun k hk => by
      have h1 := (hKids k hk).base
      have h2 := (hKids k hk).address
      have h3 := hPayload k hk
      simp only [regionsDisjoint] at h3
      omega
    have hPair := hApart
    rw [hSplit, List.append_assoc, List.map_append, List.pairwise_append] at hPair
    have hRead : (linkChildren store.mem pending (childRecords store.mem q 0 (slots.take i))).1.read64
        (slotAddress q i) = store.mem.read64 (slotAddress q i) :=
      linkChildren_read64 _ _ _ _ fun k hk => by
        obtain ⟨h1, h2, h3⟩ := hKids' k (by rw [hSplit]; simp [hk])
        refine ⟨by omega, h2, ?_⟩
        rw [hSlotAt]
        omega
    have hHeaderS : ∀ k ∈ childRecords store.mem q i [slots[i]], ChildHeader
        { store with mem := (linkChildren store.mem pending
          (childRecords store.mem q 0 (slots.take i))).1 } k.1 := fun k hk => by
      have hk' : k ∈ childRecords store.mem q 0 slots := by rw [hSplit]; simp [hk]
      have hc := hKids k hk'
      have hBase := hc.base
      have hFit := hc.address
      have hOut : ∀ k' ∈ childRecords store.mem q 0 (slots.take i), 40 ≤ k'.1.toNat ∧
          k'.1.toNat < 4294967296 ∧ (k'.1.toNat ≤ k.1.toNat - 48 ∨ k.1.toNat ≤ k'.1.toNat - 48) :=
        fun k' hk'' => by
          obtain ⟨h1, h2, -⟩ := hKids' k' (by rw [hSplit]; simp [hk''])
          have := hPair.2.2 _ (List.mem_map_of_mem hk'') _
            (List.mem_map_of_mem (List.mem_append_left _ hk))
          simp only [regionsDisjoint] at this
          omega
      have hAt (off : Nat) (hoff : off ≤ 48) (hoff8 : 32 ≤ off) :
          (linkChildren store.mem pending (childRecords store.mem q 0 (slots.take i))).1.read64
            (UInt32.ofNat (k.1.toNat - off)) = store.mem.read64 (UInt32.ofNat (k.1.toNat - off)) :=
        linkChildren_read64 _ _ _ _ fun k' hk'' => by
          obtain ⟨h1, h2, h3⟩ := hOut k' hk''
          refine ⟨h1, h2, ?_⟩
          rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          omega
      exact ⟨hBase, hFit, by simp only [linkChildren_pages]; exact hc.memory,
        (hAt 48 le_rfl (by omega)).trans hc.magic, (hAt 40 (by omega) (by omega)).trans hc.count⟩
    refine dropSlot_specA env { store with mem := (linkChildren store.mem pending
        (childRecords store.mem q 0 (slots.take i))).1 }
      ⟨root, c, (linkChildren store.mem pending (childRecords store.mem q 0 (slots.take i))).2, q,
        kind, length, UInt64.ofNat slots.length, maskOf slots, element, UInt64.ofNat i, ch,
        previous, current⟩ slots i hLt hShort rfl rfl hAddress
      (by simp only [linkChildren_pages]; exact hMemory)
      (fun hBit hNone => by
        simp only
        rw [hRead]
        exact hNull i hLt hBit (by rw [← childRecords_single_congr _ hRead]; exact hNone))
      (fun k hk => by
        simp only at hk
        rw [childRecords_single_congr _ hRead] at hk
        exact hHeaderS k hk)
      hObjectAl
      (fun k hk => by
        simp only at hk
        rw [childRecords_single_congr _ hRead] at hk
        exact hKidsAl k (by rw [hSplit]; simp [hk]))
      _ _ fun c' ch' => ?_
    have hStep : childRecords (linkChildren store.mem pending
        (childRecords store.mem q 0 (slots.take i))).1 q i [slots[i]] =
        childRecords store.mem q i [slots[i]] := childRecords_single_congr _ hRead
    have hTake : childRecords store.mem q 0 (slots.take (i + 1)) =
        childRecords store.mem q 0 (slots.take i) ++ childRecords store.mem q i [slots[i]] := by
      rw [List.take_succ_eq_append_getElem hLt, childRecords_append, List.length_take,
        min_eq_left hLt.le, Nat.zero_add]
    simp [wpA_simp, wp_simp, ReleaseVars.afterSlot, ReleaseVars.toLocals, releaseSlot, hStep]
    refine ⟨⟨i + 1, hLt, ?_⟩, ?_⟩
    · rw [hTake, linkChildren_append]
      exact ⟨rfl, rfl, by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
        simp⟩
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · have hEq : i = slots.length := by omega
    subst hEq
    simp only [List.take_length]
    simp [wpA_simp, wp_simp]
    simpa [ReleaseVars.toLocals] using hNext ⟨root, c, (linkChildren store.mem pending
      (childRecords store.mem q 0 slots)).2, q, kind, length, UInt64.ofNat slots.length,
      maskOf slots, element, UInt64.ofNat slots.length, ch, previous, current⟩ rfl rfl rfl rfl

theorem dropChildren_specA {m : Module} (env : HostEnv Unit) (store : Store Unit) (v : ReleaseVars)
    (slots : List Slot) (hBase : 48 ≤ v.object.toNat) (hShort : slots.length ≤ 64)
    (hAddress : v.object.toNat + 8 * slots.length < 4294967296)
    (hMemory : v.object.toNat + 8 * slots.length ≤ store.mem.pages * 65536)
    (hMaskWord : store.mem.read64 (v.object - 8).toUInt32 = maskOf slots)
    (hKind : maskOf slots ≠ 0 → store.mem.read64 (v.object - 24).toUInt32 = 1)
    (hWidth : maskOf slots ≠ 0 →
      store.mem.read64 (v.object - 16).toUInt32 = UInt64.ofNat slots.length)
    (hNull : ∀ i (h : i < slots.length), slots[i].bit = 1 →
      childRecords store.mem v.object i [slots[i]] = [] →
      store.mem.read64 (slotAddress v.object i) = 0)
    (hKids : ∀ k ∈ childRecords store.mem v.object 0 slots, ChildHeader store k.1)
    (hApart : ((childRecords store.mem v.object 0 slots).map fun k => (k.1.toNat - 48, 48)).Pairwise
      regionsDisjoint)
    (hPayload : ∀ k ∈ childRecords store.mem v.object 0 slots,
      regionsDisjoint (k.1.toNat - 48, 48) (v.object.toNat, 8 * slots.length))
    (hObjectAl : v.object.toNat % 8 = 0)
    (hKidsAl : ∀ k ∈ childRecords store.mem v.object 0 slots, k.1.toNat % 8 = 0)
    (Q : Assertion Unit) (after : Program)
    (hNext : ∀ v' : ReleaseVars, v'.root = v.root → v'.object = v.object →
      v'.pending = (linkChildren store.mem v.pending (childRecords store.mem v.object 0 slots)).2 →
      wpA m after Q { store with mem := (linkChildren store.mem v.pending
        (childRecords store.mem v.object 0 slots)).1 } v'.toLocals env) :
    wpA m (dropChildren ++ after) Q store v.toLocals env := by
  obtain ⟨root, count, pending, q, kind, length, width, mask, element, slot, child, previous,
    current⟩ := v
  simp only at hObjectAl hKidsAl
  simp only at hBase hAddress hMemory hMaskWord hKind hWidth hNull hKids hApart hPayload hNext ⊢
  have hSub : ∀ k : UInt64, k.toNat ≤ 48 → (q - k).toNat = q.toNat - k.toNat := fun k hk =>
    UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)
  have hA : ∀ k : UInt64, k.toNat ≤ 48 → (q - k).toUInt32 = UInt32.ofNat (q.toNat - k.toNat) :=
    fun k hk => by rw [Memory.toUInt32_eq_ofNat, hSub k hk, Nat.mod_eq_of_lt (by omega)]
  have hs8 : (q - 8).toNat = q.toNat - 8 := hSub 8 (by decide)
  have hs16 : (q - 16).toNat = q.toNat - 16 := hSub 16 (by decide)
  have hs24 : (q - 24).toNat = q.toNat - 24 := hSub 24 (by decide)
  have hm8 : (q.toNat - 8) % 4294967296 = q.toNat - 8 := Nat.mod_eq_of_lt (by omega)
  have hm16 : (q.toNat - 16) % 4294967296 = q.toNat - 16 := Nat.mod_eq_of_lt (by omega)
  have hm24 : (q.toNat - 24) % 4294967296 = q.toNat - 24 := Nat.mod_eq_of_lt (by omega)
  have hc8 : ¬ store.mem.pages * 65536 < q.toNat - 8 + 8 := by omega
  have hc16 : ¬ store.mem.pages * 65536 < q.toNat - 16 + 8 := by omega
  have hc24 : ¬ store.mem.pages * 65536 < q.toNat - 24 + 8 := by omega
  have hqa8 : (q.toNat - 8) % 8 = 0 := by omega
  have hqa16 : (q.toNat - 16) % 8 = 0 := by omega
  have hqa24 : (q.toNat - 24) % 8 = 0 := by omega
  rw [hA 8 (by decide)] at hMaskWord
  rw [hA 16 (by decide)] at hWidth
  rw [hA 24 (by decide)] at hKind
  simp only [UInt64.reduceToNat] at hMaskWord hWidth hKind
  simp [dropChildren, headerLoad, ReleaseVars.toLocals, releaseMask, releaseObject, releaseKind,
    releaseWidth, wpA_simp, wp_simp, hs8, hm8, hc8, hqa8, hMaskWord]
  by_cases hZero : maskOf slots = 0
  · have hNone := childRecords_of_mask store.mem q 0 slots hShort hZero
    simp only [hZero, ite_true]
    refine wpA_iff_cons rfl ?_
    simp [wpA_simp, wp_simp]
    simpa [ReleaseVars.toLocals, hNone, linkChildren] using hNext
      ⟨root, count, pending, q, kind, length, width, 0, element, slot, child, previous, current⟩
      rfl rfl (by simp [hNone, linkChildren])
  · simp only [hZero, ite_false]
    refine wpA_iff_cons rfl ?_
    simp [wpA_simp, wp_simp, hs24, hm24, hc24, hqa24, hKind hZero, hs16, hm16, hc16, hqa16,
      hWidth hZero]
    refine wpA_iff_cons rfl ?_
    simp only [show (if (1 : UInt32) ≠ 0 then countedLoop releaseSlot 6
        (dropMaskedSlot 7 releaseSlot releaseChild releaseCount releasePending
          [.localGet 3, .localGet releaseSlot, .constI64 8, .mulI64, .addI64]) else []) =
        countedLoop releaseSlot releaseWidth dropSlot ++ [] from rfl]
    refine slotLoop_specA env store
      ⟨root, count, pending, q, 1, length, UInt64.ofNat slots.length, maskOf slots, element, slot,
        child, previous, current⟩ slots hShort rfl rfl hAddress hMemory hNull hKids hApart
      hPayload hObjectAl hKidsAl _ _ fun v' hRoot hObject hKind' hPending => ?_
    obtain ⟨root', count', pending', q', kind', length', width', mask', element', slot', child',
      previous', current'⟩ := v'
    simp only at hRoot hObject hKind' hPending
    subst hRoot hObject hKind' hPending
    simp [wpA_simp, wp_simp, ReleaseVars.toLocals]
    refine wpA_iff_cons rfl ?_
    simp [wpA_simp, wp_simp]
    simpa [ReleaseVars.toLocals] using hNext
      ⟨root', count', _, q', 1, length', width', mask', element', slot', child', previous',
        current'⟩ rfl rfl rfl

theorem release_tree_run_topA {m : Module} {typeIdx : Nat} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx)) (env : HostEnv Unit) (heap : Heap)
    (store : Store Unit) (p : UInt64) (n : Node) (hHeap : heap.At store)
    (hOwned : NodeOwned heap store p n) (hDisjoint : (n.blocks store p).Pairwise regionsDisjoint)
    (hAligned : heap.Aligned) (hBlocksAl : ∀ b ∈ n.blocks store p, b.1 % 8 = 0 ∧ b.2 % 8 = 0) :
    RunsA false env m 1 store [.i64 p] fun final out => out = [] ∧
      ∃ heap' : Heap, heap'.At final ∧ heap'.top = heap.top ∧
        final.memoryCaps = store.memoryCaps ∧
        (∀ r, heap.Region r → 0 < r.2 → (∀ b ∈ n.blocks store p, regionsDisjoint r b) →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r) ∧ heap'.Aligned := by
  refine RunsA.of_wpA_entry_for (f := releaseFunction typeIdx)
    (by simpa [hImports] using hFunc) ?_ (by simp [hImports])
  cases n with
  | null =>
    have hp : p = 0 := hOwned
    subst hp
    simp [releaseFunction, releaseBody, Function.toLocals, Function.numParams, ValueType.zero,
      TrapMsg, wpA_simp, wp_simp]
    refine wpA_iff_cons rfl ?_
    simp [wpA_simp, wp_simp]
    exact ⟨heap, hHeap, rfl, fun a b hr _ _ => hr, hAligned⟩
  | record slots =>
    obtain ⟨hHeader, hSlots⟩ := hOwned
    have hBase := hHeader.base
    have hFit := hHeader.address
    have hBelow := hHeader.below
    have hTop := hHeap.top
    have hPtr : p ≠ 0 := by rintro rfl; simp at hBase
    have hs48 : (p - 48).toNat = p.toNat - 48 := UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; simp; omega)
    have hs40 : (p - 40).toNat = p.toNat - 40 := UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le]; simp; omega)
    have hm48 : (p.toNat - 48) % 4294967296 = p.toNat - 48 := Nat.mod_eq_of_lt (by omega)
    have hm40 : (p.toNat - 40) % 4294967296 = p.toNat - 40 := Nat.mod_eq_of_lt (by omega)
    have hc48 : ¬ store.mem.pages * 65536 < p.toNat - 48 + 8 := by simp only [capacityAt] at *; omega
    have hc40 : ¬ store.mem.pages * 65536 < p.toNat - 40 + 8 := by simp only [capacityAt] at *; omega
    have hMagic := (hHeader.childHeader hHeap).magic
    have hCount := (hHeader.childHeader hHeap).count
    have hpBlock := hBlocksAl (block store p) List.mem_cons_self
    simp only [block] at hpBlock
    have hpa48 : (p.toNat - 48) % 8 = 0 := hpBlock.1
    have hpa40 : (p.toNat - 40) % 8 = 0 := by omega
    simp [releaseFunction, releaseBody, dropReference, checkMagic, headerLoad, headerStore,
      releaseCount, releasePending, releaseObject, Function.toLocals, Function.numParams,
      ValueType.zero, TrapMsg, wpA_simp, wp_simp, hPtr]
    refine wpA_iff_cons rfl ?_
    have hb48 : p.toNat - 48 + 8 ≤ store.mem.pages * 65536 := by omega
    have hb40 : p.toNat - 40 + 8 ≤ store.mem.pages * 65536 := by omega
    simp [wpA_simp, wp_simp, hs48, hm48, hb48, hpa48, hMagic]
    refine wpA_iff_cons rfl ?_
    simp [wpA_simp, wp_simp, hs40, hm40, hb40, hpa40, hCount]
    refine wpA_iff_cons rfl ?_
    simp [wpA_simp, wp_simp, hs40, hm40, hb40, hpa40]
    obtain ⟨hStart, hStartBlocks⟩ := Releasing.startBlocks hHeap ⟨hHeader, hSlots⟩ hDisjoint
    refine wpA_block_cons ?_
    refine wpA_loop_ghost (fun k st s => ∃ (heap' : Heap) (v : ReleaseVars)
        (items : List (UInt64 × List Slot)), s = v.toLocals ∧ v.root = p ∧
        forestRecords items = k ∧
        Releasing heap store (Node.blocks store p (.record slots)) heap' st v.pending items ∧
        heap'.Aligned ∧ ∀ b ∈ forestBlocks st items, b.1 % 8 = 0 ∧ b.2 % 8 = 0)
      (forestRecords [(p, slots)])
      ⟨heap, ⟨p, 1, p, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, [(p, slots)], by
        simp [ReleaseVars.toLocals], rfl, rfl, hStart, hAligned,
        fun b hb => hBlocksAl b (by rw [← hStartBlocks]; exact hb)⟩ ?_
    rintro k st s ⟨heap', v, items, rfl, hRoot, rfl, hR, hHeapAl, hItemsAl⟩
    obtain ⟨root, count, pending, object, kind, length, width, mask, element, slot, child,
      previous, current⟩ := v
    simp only at hRoot hR
    subst hRoot
    cases items with
    | nil =>
      obtain ⟨hPending, hAt', hCaps', hFrame'⟩ := hR.done
      subst hPending
      simp [ReleaseVars.toLocals, wpA_simp, wp_simp]
      exact ⟨heap', hAt', hR.top, hCaps', fun a b hr hb hT =>
        hFrame' (a, b) hr hb fun x hx => hT x.1 x.2 hx, hHeapAl⟩
    | cons item rest =>
      obtain ⟨q, qslots⟩ := item
      obtain ⟨hPending, hqBase, hShort, hqAddress, hqMemory, hMaskWord, hKindWord, hWidthWord,
        hNull, hKids, hApart, hPayload⟩ := hR.dropFacts
      subst hPending
      have hqBase' := ((hR.records _ List.mem_cons_self).1).base
      have hq0 : pending ≠ 0 := by rintro rfl; simp at hqBase'
      have hqs40 : (pending - 40).toNat = pending.toNat - 40 := UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]; simp; omega)
      have hqm40 : (pending.toNat - 40) % 4294967296 = pending.toNat - 40 :=
        Nat.mod_eq_of_lt (by omega)
      have hqb40 : pending.toNat - 40 + 8 ≤ st.mem.pages * 65536 := by omega
      have hqBlock := hItemsAl (block st pending) (by rw [forestBlocks_cons]; exact List.mem_cons_self)
      simp only [block] at hqBlock
      have hqAl : pending.toNat % 8 = 0 := by omega
      have hqCapAl : capacityAt st pending % 8 = 0 := by omega
      have hqa40 : (pending.toNat - 40) % 8 = 0 := by omega
      have hKidsAl : ∀ k ∈ childRecords st.mem pending 0 qslots, k.1.toNat % 8 = 0 := fun k hk => by
        have hb := hItemsAl (block st k.1) (by
          rw [forestBlocks_cons]
          exact List.mem_cons_of_mem _ (List.mem_append_left _
            (List.mem_flatMap.mpr ⟨k, hk, mem_blocks_record st k⟩)))
        have := (hKids k hk).base
        simp only [block] at hb
        omega
      simp [ReleaseVars.toLocals, wpA_simp, wp_simp, hq0, hqs40, hqm40, hqb40, hqa40]
      obtain ⟨⟨hAt1, hObj1, hR', hLt⟩, hCap1, hBlocksSub⟩ := hR.nextBlocks
      refine dropChildren_specA env st
        ⟨root, count, st.mem.read64 (UInt32.ofNat (pending.toNat - 40)), pending, kind, length,
          width, mask, element, slot, child, previous, current⟩ qslots hqBase hShort hqAddress
        hqMemory hMaskWord hKindWord hWidthWord hNull hKids hApart hPayload hqAl hKidsAl _ _
        fun v' hRoot' hObj' hPend' => ?_
      simp only at hRoot' hObj' hPend'
      refine freeObject_specA env heap' _ v' hAt1 (by rw [hObj']; exact hObj1) hHeapAl.roots
        (by rw [hObj']; exact hqAl) _ _ fun prev cur => ?_
      rw [hObj']
      simp [wpA_simp, wp_simp]
      exact ⟨_, v'.atPlace prev cur, _, hLt, ⟨rfl, rfl⟩,
        by simpa [ReleaseVars.atPlace] using hRoot', by
          simp only [ReleaseVars.atPlace]
          rw [hPend']
          exact hR',
        hHeapAl.release hqAl (by have := hCap1; simp only [capacityAt] at this hqCapAl ⊢; omega),
        fun a b hab => hItemsAl (a, b) (hBlocksSub (a, b) hab)⟩

end LeanExe.Pipeline
