import Project.Pipeline.RuntimeSpec
import Project.Pipeline.Records

/-!
`release` on a tree of records.  The runtime's loop takes the head of the pending list,
links the non-null children of its masked slots onto the front of the list through their
count words, and frees the record.
-/

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/- As in `RuntimeSpec.lean`: CodeLib's `Mem.read64_write64_same` is proved with
`bv_decide`, and the kernel-checked `Memory.read64_write64` replaces it. -/
attribute [-simp] Wasm.Mem.read64_write64_same
attribute [local simp] Memory.read64_write64

/-- A loop rule whose measure is a ghost index in the invariant: each iteration that
branches back re-enters the invariant at a smaller index. -/
theorem wp_loop_ghost {α : Type} {m : Module} {env : HostEnv α} {ps rs : Nat}
    {body rest : Program} {Q : Assertion α} {st : Store α} {s : Locals}
    (Inv : Nat → AssertionF α) (n : Nat) (hInit : Inv n st s)
    (hStep : ∀ n st s, Inv n st s →
        wp m body
          (fun c => match c with
            | .Fallthrough st' s' =>
              wp m rest Q st' { s' with values := s'.values.take rs ++ s.values.drop ps } env
            | .Break 0 st' s' =>
              ∃ n' < n, Inv n' st' { s' with values := s'.values.take ps ++ s.values.drop ps }
            | .Break (k+1) st' s' => Q (.Break k st' s')
            | other => Q other)
          st s env) :
    wp m (.loop ps rs body :: rest) Q st s env := by
  classical
  refine wp_loop_cons (fun st s => ∃ n, Inv n st s)
    (fun st s => if h : ∃ n, Inv n st s then Nat.find h else 0) ⟨n, hInit⟩ ?_
  intro st s hEx
  refine wp.conseq ?_ (hStep _ st s (Nat.find_spec hEx))
  intro c hc
  rcases c with ⟨st', s'⟩ | ⟨_ | k, st', s'⟩ | _ | _ | _ | _ | _ | _
  · exact hc
  · obtain ⟨n', hlt, hInv⟩ := hc
    refine ⟨⟨n', hInv⟩, ?_⟩
    rw [dite_eq_left_of_eq_true (eq_true ⟨n', hInv⟩), dite_eq_left_of_eq_true (eq_true hEx)]
    exact lt_of_le_of_lt (Nat.find_min' _ hInv) hlt
  all_goals exact hc

/-- `v` after `dropReference` links the child onto the pending list. -/
def ReleaseVars.link (v : ReleaseVars) : ReleaseVars := { v with count := 1, pending := v.child }

/-- `dropReference` on the child in local `child`: with the magic number and count 1 in the
child's header, it links the child onto the pending list through its count word. -/
theorem dropReference_spec {m : Module} (env : HostEnv Unit) (store : Store Unit)
    (v : ReleaseVars) (hBase : 48 ≤ v.child.toNat) (hFit : v.child.toNat < 4294967296)
    (hMemory : v.child.toNat ≤ store.mem.pages * 65536)
    (hMagic : store.mem.read64 (UInt32.ofNat (v.child.toNat - 48)) = magic)
    (hCount : store.mem.read64 (UInt32.ofNat (v.child.toNat - 40)) = 1)
    (Q : Assertion Unit) (after : Program)
    (hNext : wp m after Q
      { store with mem := store.mem.write64 (UInt32.ofNat (v.child.toNat - 40)) v.pending }
      v.link.toLocals env) :
    wp m (dropReference releaseChild releaseCount releasePending ++ after) Q store
      v.toLocals env := by
  obtain ⟨root, count, pending, object, kind, length, width, mask, element, slot, ptr, previous,
    current⟩ := v
  simp only [ReleaseVars.link] at hNext hBase hFit hMemory hMagic hCount ⊢
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
  simp [dropReference, checkMagic, headerLoad, headerStore, ReleaseVars.toLocals, releaseChild,
    releaseCount, releasePending, wp_simp, hs48, hm48, hc48, hMagic]
  refine wp_iff_cons rfl ?_
  simp [wp_simp, hs40, hm40, hc40, hCount]
  refine wp_iff_cons rfl ?_
  simp [wp_simp, hs40, hm40, hc40]
  exact hNext

/-- The non-null children of slots `i` on of the record at `p`, with their slots. -/
def childRecords (mem : Mem) (p : UInt64) (i : Nat) : List Slot → List (UInt64 × List Slot)
  | [] => []
  | .word _ :: rest => childRecords mem p (i + 1) rest
  | .child .null :: rest => childRecords mem p (i + 1) rest
  | .child (.record cs) :: rest =>
      (mem.read64 (slotAddress p i), cs) :: childRecords mem p (i + 1) rest

/-- The memory and pending head after linking `children`, in order, onto the pending list
whose head is `pending`, through their count words. -/
def linkChildren (mem : Mem) (pending : UInt64) : List (UInt64 × List Slot) → Mem × UInt64
  | [] => (mem, pending)
  | (c, _) :: rest => linkChildren (mem.write64 (UInt32.ofNat (c.toNat - 40)) pending) c rest

/-- The loop body of `dropChildren` for a record. -/
def dropSlot : Program :=
  dropMaskedSlot releaseMask releaseSlot releaseChild releaseCount releasePending
    [.localGet releaseObject, .localGet releaseSlot, .constI64 8, .mulI64, .addI64]

/-- `v` with the locals that one slot step changes. -/
def ReleaseVars.afterSlot (v : ReleaseVars) (count child pending : UInt64) : ReleaseVars :=
  { v with count := count, child := child, pending := pending }

/-- The header facts of a child that `dropReference` reads: the magic number and count 1,
with the header inside memory and the 32-bit address space. -/
structure ChildHeader (store : Store Unit) (c : UInt64) : Prop where
  base : 48 ≤ c.toNat
  address : c.toNat < 4294967296
  memory : c.toNat ≤ store.mem.pages * 65536
  magic : store.mem.read64 (UInt32.ofNat (c.toNat - 48)) = magic
  count : store.mem.read64 (UInt32.ofNat (c.toNat - 40)) = 1

/-- One step of the slot loop for slot `i`: a word slot and a null child change nothing,
and a record child is linked onto the pending list. -/
theorem dropSlot_spec {m : Module} (env : HostEnv Unit) (store : Store Unit) (v : ReleaseVars)
    (slots : List Slot) (i : Nat) (hi : i < slots.length) (hShort : slots.length ≤ 64)
    (hMask : v.mask = maskOf slots) (hSlotLocal : v.slot = UInt64.ofNat i)
    (hAddress : v.object.toNat + 8 * slots.length < 4294967296)
    (hMemory : v.object.toNat + 8 * slots.length ≤ store.mem.pages * 65536)
    (hNull : slots[i] = .child .null → store.mem.read64 (slotAddress v.object i) = 0)
    (hRecord : ∀ cs, slots[i] = .child (.record cs) →
      ChildHeader store (store.mem.read64 (slotAddress v.object i)))
    (Q : Assertion Unit) (after : Program)
    (hNext : ∀ count child, wp m after Q
      { store with mem := (linkChildren store.mem v.pending
        (childRecords store.mem v.object i [slots[i]])).1 }
      (v.afterSlot count child (linkChildren store.mem v.pending
        (childRecords store.mem v.object i [slots[i]])).2).toLocals env) :
    wp m (dropSlot ++ after) Q store v.toLocals env := by
  obtain ⟨root, count, pending, q, kind, length, width, mask, element, slot, child, previous,
    current⟩ := v
  simp only at hMask hSlotLocal hAddress hMemory hNull hRecord hNext ⊢
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
    releaseCount, releasePending, releaseObject, wp_simp, hTest]
  generalize hs : slots[i] = s at hNull hRecord hNext
  cases s with
  | word w =>
    simp [Slot.bit]
    refine wp_iff_cons rfl ?_
    simp [wp_simp]
    simpa [childRecords, linkChildren, ReleaseVars.afterSlot, ReleaseVars.toLocals] using
      hNext count child
  | child n =>
    have hmod : (q.toNat + i * 8) % 4294967296 = q.toNat + i * 8 := Nat.mod_eq_of_lt (by omega)
    have hAddrEq : UInt32.ofNat (q.toNat + i * 8) = slotAddress q i :=
      UInt32.toNat_inj.mp (by rw [hSlotAt, UInt32.toNat_ofNat']; omega)
    simp [Slot.bit]
    refine wp_iff_cons rfl ?_
    have hb2 : ¬ store.mem.pages * 65536 < (slotAddress q i).toNat + 8 := by omega
    simp [wp_simp, hmod, hAddrEq, hb2]
    cases n with
    | null =>
      simp [hNull rfl]
      refine wp_iff_cons rfl ?_
      simp [wp_simp]
      simpa [childRecords, linkChildren, ReleaseVars.afterSlot, ReleaseVars.toLocals] using
        hNext count 0
    | record cs =>
      have hc := hRecord cs rfl
      have hNe : store.mem.read64 (slotAddress q i) ≠ 0 := by
        intro h
        have := hc.base
        rw [h] at this
        simp at this
      simp [hNe]
      refine wp_iff_cons rfl ?_
      rw [show (if ¬(1 : UInt32) = 0 then dropReference 10 1 2 else []) = dropReference 10 1 2
        from rfl, ← List.append_nil (dropReference 10 1 2)]
      refine dropReference_spec env store
        ⟨root, count, pending, q, kind, length, width, maskOf slots, element, UInt64.ofNat i,
          store.mem.read64 (slotAddress q i), previous, current⟩ hc.base hc.address hc.memory
        hc.magic hc.count _ _ ?_
      simp [wp_simp]
      simpa [childRecords, linkChildren, ReleaseVars.afterSlot, ReleaseVars.link,
        ReleaseVars.toLocals] using hNext 1 (store.mem.read64 (slotAddress q i))

theorem childRecords_append (mem : Mem) (p : UInt64) :
    ∀ (i : Nat) (xs ys : List Slot),
      childRecords mem p i (xs ++ ys) = childRecords mem p i xs ++ childRecords mem p (i + xs.length) ys
  | _, [], _ => by simp [childRecords]
  | i, .word _ :: xs, ys => by
      simp [childRecords, childRecords_append mem p (i + 1) xs ys, Nat.add_assoc, Nat.add_comm 1]
  | i, .child .null :: xs, ys => by
      simp [childRecords, childRecords_append mem p (i + 1) xs ys, Nat.add_assoc, Nat.add_comm 1]
  | i, .child (.record _) :: xs, ys => by
      simp [childRecords, childRecords_append mem p (i + 1) xs ys, Nat.add_assoc, Nat.add_comm 1]

theorem linkChildren_append (mem : Mem) (pending : UInt64) :
    ∀ (xs ys : List (UInt64 × List Slot)),
      linkChildren mem pending (xs ++ ys) =
        linkChildren (linkChildren mem pending xs).1 (linkChildren mem pending xs).2 ys
  | [], _ => rfl
  | (c, _) :: xs, ys => linkChildren_append _ c xs ys

theorem linkChildren_pages (mem : Mem) (pending : UInt64) :
    ∀ (ks : List (UInt64 × List Slot)), (linkChildren mem pending ks).1.pages = mem.pages
  | [] => rfl
  | (c, _) :: ks => by
      rw [linkChildren, linkChildren_pages _ c ks, Wasm.Mem.write64_pages]

/-- Linking children changes only their count words. -/
theorem linkChildren_bytes (mem : Mem) (pending : UInt64) (a : Nat) :
    ∀ (ks : List (UInt64 × List Slot)),
      (∀ k ∈ ks, 40 ≤ k.1.toNat ∧ k.1.toNat < 4294967296 ∧
        (a < k.1.toNat - 40 ∨ k.1.toNat - 32 ≤ a)) →
      (linkChildren mem pending ks).1.bytes a = mem.bytes a
  | [], _ => rfl
  | (c, _) :: ks, h => by
      rw [linkChildren, linkChildren_bytes _ c a ks fun k hk => h k (List.mem_cons_of_mem _ hk)]
      obtain ⟨h40, hFit, hOut⟩ := h (c, _) List.mem_cons_self
      simp only at h40 hFit hOut
      refine Memory.write64_bytes_outside _ _ _ ?_
      rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      omega

theorem childRecords_split (mem : Mem) (p : UInt64) (slots : List Slot) (i : Nat)
    (hi : i < slots.length) :
    childRecords mem p 0 slots = childRecords mem p 0 (slots.take i) ++
      childRecords mem p i [slots[i]] ++ childRecords mem p (i + 1) (slots.drop (i + 1)) := by
  conv_lhs => rw [← List.take_append_drop i slots, List.drop_eq_getElem_cons hi]
  rw [childRecords_append, show slots[i] :: slots.drop (i + 1) = [slots[i]] ++ slots.drop (i + 1)
    from rfl, childRecords_append, List.length_take, min_eq_left hi.le, List.append_assoc]
  simp

theorem linkChildren_read64 (mem : Mem) (pending : UInt64) (address : UInt32)
    (ks : List (UInt64 × List Slot))
    (h : ∀ k ∈ ks, 40 ≤ k.1.toNat ∧ k.1.toNat < 4294967296 ∧
      (address.toNat + 8 ≤ k.1.toNat - 40 ∨ k.1.toNat - 32 ≤ address.toNat)) :
    (linkChildren mem pending ks).1.read64 address = mem.read64 address :=
  Memory.read64_congr address fun j hj => linkChildren_bytes mem pending _ ks fun k hk => by
    obtain ⟨h40, hFit, hOut⟩ := h k hk
    exact ⟨h40, hFit, by omega⟩

theorem childRecords_single_congr {m1 m2 : Mem} {p : UInt64} {i : Nat} (s : Slot)
    (h : m1.read64 (slotAddress p i) = m2.read64 (slotAddress p i)) :
    childRecords m1 p i [s] = childRecords m2 p i [s] := by
  rcases s with _ | (_ | _) <;> simp [childRecords, h]

/-- The slot loop of `dropChildren` for the record at `v.object`, whose mask and width
locals describe `slots`, links its non-null children onto the pending list in slot order.
The children's headers lie apart from each other and from the record's slots. -/
theorem slotLoop_spec {m : Module} (env : HostEnv Unit) (store : Store Unit) (v : ReleaseVars)
    (slots : List Slot) (hShort : slots.length ≤ 64)
    (hMask : v.mask = maskOf slots) (hWidth : v.width = UInt64.ofNat slots.length)
    (hAddress : v.object.toNat + 8 * slots.length < 4294967296)
    (hMemory : v.object.toNat + 8 * slots.length ≤ store.mem.pages * 65536)
    (hNull : ∀ i (h : i < slots.length), slots[i] = .child .null →
      store.mem.read64 (slotAddress v.object i) = 0)
    (hKids : ∀ k ∈ childRecords store.mem v.object 0 slots, ChildHeader store k.1)
    (hApart : ((childRecords store.mem v.object 0 slots).map fun k => (k.1.toNat - 48, 48)).Pairwise
      regionsDisjoint)
    (hPayload : ∀ k ∈ childRecords store.mem v.object 0 slots,
      regionsDisjoint (k.1.toNat - 48, 48) (v.object.toNat, 8 * slots.length))
    (Q : Assertion Unit) (after : Program)
    (hNext : ∀ v' : ReleaseVars, v'.root = v.root → v'.object = v.object → v'.kind = v.kind →
      v'.pending = (linkChildren store.mem v.pending (childRecords store.mem v.object 0 slots)).2 →
      wp m after Q { store with mem := (linkChildren store.mem v.pending
        (childRecords store.mem v.object 0 slots)).1 } v'.toLocals env) :
    wp m (countedLoop releaseSlot releaseWidth dropSlot ++ after) Q store v.toLocals env := by
  obtain ⟨root, count, pending, q, kind, length, width, mask, element, slot, child, previous,
    current⟩ := v
  simp only at hMask hWidth hAddress hMemory hNull hKids hApart hPayload hNext ⊢
  subst hMask hWidth
  simp [countedLoop, ReleaseVars.toLocals, releaseSlot, releaseWidth, wp_simp]
  apply wp_block_cons
  refine wp_loop_cons (fun st s => ∃ i, i ≤ slots.length ∧
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
  simp [ReleaseVars.toLocals, wp_simp]
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
    refine dropSlot_spec env { store with mem := (linkChildren store.mem pending
        (childRecords store.mem q 0 (slots.take i))).1 }
      ⟨root, c, (linkChildren store.mem pending (childRecords store.mem q 0 (slots.take i))).2, q,
        kind, length, UInt64.ofNat slots.length, maskOf slots, element, UInt64.ofNat i, ch,
        previous, current⟩ slots i hLt hShort rfl rfl hAddress
      (by simp only [linkChildren_pages]; exact hMemory)
      (fun h => by simp only; rw [hRead]; exact hNull i hLt h)
      (fun cs h => by
        simp only
        rw [hRead]
        exact hHeaderS (store.mem.read64 (slotAddress q i), cs) (by simp [h, childRecords]))
      _ _ fun c' ch' => ?_
    have hStep : childRecords (linkChildren store.mem pending
        (childRecords store.mem q 0 (slots.take i))).1 q i [slots[i]] =
        childRecords store.mem q i [slots[i]] := childRecords_single_congr _ hRead
    have hTake : childRecords store.mem q 0 (slots.take (i + 1)) =
        childRecords store.mem q 0 (slots.take i) ++ childRecords store.mem q i [slots[i]] := by
      rw [List.take_succ_eq_append_getElem hLt, childRecords_append, List.length_take,
        min_eq_left hLt.le, Nat.zero_add]
    simp [wp_simp, ReleaseVars.afterSlot, ReleaseVars.toLocals, releaseSlot, hStep]
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
    simp [wp_simp]
    simpa [ReleaseVars.toLocals] using hNext ⟨root, c, (linkChildren store.mem pending
      (childRecords store.mem q 0 slots)).2, q, kind, length, UInt64.ofNat slots.length,
      maskOf slots, element, UInt64.ofNat slots.length, ch, previous, current⟩ rfl rfl rfl rfl

theorem childRecords_words (mem : Mem) (p : UInt64) :
    ∀ (i : Nat) (slots : List Slot), (∀ s ∈ slots, s.bit = 0) → childRecords mem p i slots = []
  | _, [], _ => rfl
  | i, .word _ :: rest, h => childRecords_words mem p (i + 1) rest fun s hs => h s (by simp [hs])
  | _, .child _ :: _, h => absurd (h _ List.mem_cons_self) (by simp [Slot.bit])

/-- A record whose mask is 0 has no children. -/
theorem childRecords_of_mask (mem : Mem) (p : UInt64) (i : Nat) (slots : List Slot)
    (hShort : slots.length ≤ 64) (hMask : maskOf slots = 0) : childRecords mem p i slots = [] := by
  obtain ⟨-, hBits⟩ := maskOf_toNat slots hShort
  refine childRecords_words mem p i slots fun s hs => ?_
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  have := hBits j hj
  rw [hMask] at this
  simp at this
  exact UInt64.toNat_inj.mp (by rw [← this]; rfl)

/-- `dropChildren` on a record whose header holds kind 1, its width, and its mask links the
record's non-null children onto the pending list in slot order. -/
theorem dropChildren_spec {m : Module} (env : HostEnv Unit) (store : Store Unit) (v : ReleaseVars)
    (slots : List Slot) (hBase : 48 ≤ v.object.toNat) (hShort : slots.length ≤ 64)
    (hAddress : v.object.toNat + 8 * slots.length < 4294967296)
    (hMemory : v.object.toNat + 8 * slots.length ≤ store.mem.pages * 65536)
    (hMaskWord : store.mem.read64 (v.object - 8).toUInt32 = maskOf slots)
    (hKind : store.mem.read64 (v.object - 24).toUInt32 = 1)
    (hWidth : store.mem.read64 (v.object - 16).toUInt32 = UInt64.ofNat slots.length)
    (hNull : ∀ i (h : i < slots.length), slots[i] = .child .null →
      store.mem.read64 (slotAddress v.object i) = 0)
    (hKids : ∀ k ∈ childRecords store.mem v.object 0 slots, ChildHeader store k.1)
    (hApart : ((childRecords store.mem v.object 0 slots).map fun k => (k.1.toNat - 48, 48)).Pairwise
      regionsDisjoint)
    (hPayload : ∀ k ∈ childRecords store.mem v.object 0 slots,
      regionsDisjoint (k.1.toNat - 48, 48) (v.object.toNat, 8 * slots.length))
    (Q : Assertion Unit) (after : Program)
    (hNext : ∀ v' : ReleaseVars, v'.root = v.root → v'.object = v.object →
      v'.pending = (linkChildren store.mem v.pending (childRecords store.mem v.object 0 slots)).2 →
      wp m after Q { store with mem := (linkChildren store.mem v.pending
        (childRecords store.mem v.object 0 slots)).1 } v'.toLocals env) :
    wp m (dropChildren ++ after) Q store v.toLocals env := by
  obtain ⟨root, count, pending, q, kind, length, width, mask, element, slot, child, previous,
    current⟩ := v
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
  rw [hA 8 (by decide)] at hMaskWord
  rw [hA 16 (by decide)] at hWidth
  rw [hA 24 (by decide)] at hKind
  simp only [UInt64.reduceToNat] at hMaskWord hWidth hKind
  simp [dropChildren, headerLoad, ReleaseVars.toLocals, releaseMask, releaseObject, releaseKind,
    releaseWidth, wp_simp, hs8, hm8, hc8, hMaskWord]
  by_cases hZero : maskOf slots = 0
  · have hNone := childRecords_of_mask store.mem q 0 slots hShort hZero
    simp only [hZero, ite_true]
    refine wp_iff_cons rfl ?_
    simp [wp_simp]
    simpa [ReleaseVars.toLocals, hNone, linkChildren] using hNext
      ⟨root, count, pending, q, kind, length, width, 0, element, slot, child, previous, current⟩
      rfl rfl (by simp [hNone, linkChildren])
  · simp only [hZero, ite_false]
    refine wp_iff_cons rfl ?_
    simp [wp_simp, hs24, hm24, hc24, hKind, hs16, hm16, hc16, hWidth]
    refine wp_iff_cons rfl ?_
    simp only [show (if (1 : UInt32) ≠ 0 then countedLoop releaseSlot 6
        (dropMaskedSlot 7 releaseSlot releaseChild releaseCount releasePending
          [.localGet 3, .localGet releaseSlot, .constI64 8, .mulI64, .addI64]) else []) =
        countedLoop releaseSlot releaseWidth dropSlot ++ [] from rfl]
    refine slotLoop_spec env store
      ⟨root, count, pending, q, 1, length, UInt64.ofNat slots.length, maskOf slots, element, slot,
        child, previous, current⟩ slots hShort rfl rfl hAddress hMemory hNull hKids hApart
      hPayload _ _ fun v' hRoot hObject hKind' hPending => ?_
    obtain ⟨root', count', pending', q', kind', length', width', mask', element', slot', child',
      previous', current'⟩ := v'
    simp only at hRoot hObject hKind' hPending
    subst hRoot hObject hKind' hPending
    simp [wp_simp, ReleaseVars.toLocals]
    refine wp_iff_cons rfl ?_
    simp [wp_simp]
    simpa [ReleaseVars.toLocals] using hNext
      ⟨root', count', _, q', 1, length', width', mask', element', slot', child', previous',
        current'⟩ rfl rfl rfl

end Project.Pipeline
