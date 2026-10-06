import Project.Pipeline.RuntimeSpec
import Project.Pipeline.Records

/-!
`release` on a tree of records.  The runtime's loop takes the head of the pending list,
links the non-null children of its masked slots onto the front of the list through their
count words, and frees the record.
-/

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/- Use the same kernel-checked memory lemma as RuntimeSpec. -/
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
      rw [linkChildren, linkChildren_pages _ c ks, Project.TalosPrelude.write64_pages]

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

/-- A pending record: the header facts of `RecordHeader` except the count word, which holds
the link to the next pending record. -/
structure RecordBody (heap : Heap) (store : Store Unit) (p : UInt64) (slots : List Slot) :
    Prop where
  base : 4096 + 48 ≤ p.toNat
  kind : store.mem.read64 (p - 24).toUInt32 = 1
  width : store.mem.read64 (p - 16).toUInt32 = UInt64.ofNat slots.length
  mask : store.mem.read64 (p - 8).toUInt32 = maskOf slots
  short : slots.length ≤ 64
  capacity : 8 * slots.length ≤ capacityAt store p
  address : p.toNat + capacityAt store p < 4294967296
  below : p.toNat + capacityAt store p ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free,
    regionsDisjoint node.region (p.toNat - 48, 48 + capacityAt store p)

theorem RecordHeader.body {heap : Heap} {store : Store Unit} {p : UInt64} {slots : List Slot}
    (h : RecordHeader heap store p slots) : RecordBody heap store p slots :=
  ⟨h.base, h.kind, h.width, h.mask, h.short, h.capacity, h.address, h.below, h.separate⟩

/-- The pending list from `head`: each record's count word holds the next record, and the
last holds 0. -/
def PendingAt (mem : Mem) : UInt64 → List (UInt64 × List Slot) → Prop
  | head, [] => head = 0
  | head, (p, _) :: rest => head = p ∧ PendingAt mem (mem.read64 (UInt32.ofNat (p.toNat - 40))) rest

/-- The blocks of pending records and their subtrees. -/
def forestBlocks (store : Store Unit) (items : List (UInt64 × List Slot)) : List (Nat × Nat) :=
  items.flatMap fun k => Node.blocks store k.1 (.record k.2)

mutual
/-- The number of records of a value. -/
def Node.records : Node → Nat
  | .null => 0
  | .record slots => 1 + slotsRecords slots

def slotsRecords : List Slot → Nat
  | [] => 0
  | .word _ :: rest => slotsRecords rest
  | .child n :: rest => n.records + slotsRecords rest
end

/-- The number of records of the pending records and their subtrees. -/
def forestRecords (items : List (UInt64 × List Slot)) : Nat :=
  (items.map fun k => (Node.record k.2).records).sum

theorem SlotsOwned.childRecords {heap : Heap} {store : Store Unit} {p : UInt64} :
    ∀ (i : Nat) (slots : List Slot), SlotsOwned heap store p i slots →
      ∀ k ∈ childRecords store.mem p i slots, NodeOwned heap store k.1 (.record k.2)
  | _, [], _, _, hk => nomatch hk
  | i, .word _ :: rest, ⟨_, hRest⟩, k, hk => SlotsOwned.childRecords (i + 1) rest hRest k hk
  | i, .child .null :: rest, ⟨_, hRest⟩, k, hk => SlotsOwned.childRecords (i + 1) rest hRest k hk
  | i, .child (.record cs) :: rest, ⟨hChild, hRest⟩, k, hk => by
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hChild
      · exact SlotsOwned.childRecords (i + 1) rest hRest k hk

theorem SlotsOwned.null {heap : Heap} {store : Store Unit} {p : UInt64} :
    ∀ (i : Nat) (slots : List Slot), SlotsOwned heap store p i slots →
      ∀ j (h : j < slots.length), slots[j] = .child .null →
        store.mem.read64 (slotAddress p (i + j)) = 0
  | _, [], _, _, h, _ => absurd h (by simp)
  | i, s :: rest, hSlots, 0, _, hj => by
      simp only [List.getElem_cons_zero] at hj
      subst hj
      exact hSlots.1
  | i, s :: rest, hSlots, j + 1, h, hj => by
      simp only [List.getElem_cons_succ] at hj
      have hRest : SlotsOwned heap store p (i + 1) rest := by
        rcases s with _ | _ <;> exact hSlots.2
      rw [show i + (j + 1) = i + 1 + j by omega]
      exact SlotsOwned.null (i + 1) rest hRest j (by simp at h; omega) hj

theorem slotsBlocks_childRecords (store : Store Unit) (p : UInt64) :
    ∀ (i : Nat) (slots : List Slot), slotsBlocks store p i slots =
      (childRecords store.mem p i slots).flatMap fun k => Node.blocks store k.1 (.record k.2)
  | _, [] => rfl
  | i, .word _ :: rest => by
      simp only [slotsBlocks, childRecords]
      exact slotsBlocks_childRecords store p (i + 1) rest
  | i, .child .null :: rest => by
      simp only [slotsBlocks, childRecords, Node.blocks, List.nil_append]
      exact slotsBlocks_childRecords store p (i + 1) rest
  | i, .child (.record cs) :: rest => by
      simp only [slotsBlocks, childRecords, List.flatMap_cons]
      rw [slotsBlocks_childRecords store p (i + 1) rest]

theorem slotsRecords_childRecords (mem : Mem) (p : UInt64) :
    ∀ (i : Nat) (slots : List Slot), slotsRecords slots =
      forestRecords (childRecords mem p i slots)
  | _, [] => rfl
  | i, .word _ :: rest => by
      simp only [slotsRecords, childRecords]
      exact slotsRecords_childRecords mem p (i + 1) rest
  | i, .child .null :: rest => by
      simp only [slotsRecords, childRecords, Node.records, Nat.zero_add]
      exact slotsRecords_childRecords mem p (i + 1) rest
  | i, .child (.record cs) :: rest => by
      simp only [slotsRecords, childRecords, forestRecords, List.map_cons, List.sum_cons]
      rw [slotsRecords_childRecords mem p (i + 1) rest, forestRecords]

/-- A pending record keeps its header facts and capacity when the bytes of its header
words from the capacity on are unchanged and its block stays a region of the new heap. -/
theorem RecordBody.frame {heap heap' : Heap} {store store' : Store Unit} {p : UInt64}
    {slots : List Slot} (h : RecordBody heap store p slots)
    (hBytes : ∀ a, p.toNat - 32 ≤ a → a < p.toNat → store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (block store p)) :
    RecordBody heap' store' p slots ∧ capacityAt store' p = capacityAt store p := by
  have hBase := h.base
  have hAddress := h.address
  have hHeader : ∀ k : UInt64, k.toNat ≤ 32 → 8 ≤ k.toNat →
      store'.mem.read64 (p - k).toUInt32 = store.mem.read64 (p - k).toUInt32 :=
    fun k hk h8 => Memory.read64_congr _ fun i hi => by
      rw [headerAddress_toNat (by omega) (by omega)]
      exact hBytes _ (by omega) (by omega)
  have hCapacity : capacityAt store' p = capacityAt store p := by
    unfold capacityAt
    rw [hHeader 32 (by decide) (by decide)]
  have hBelow := hRegion.below
  have hSeparate := hRegion.separate
  simp only [block] at hBelow hSeparate
  refine ⟨⟨hBase, ?_, ?_, ?_, h.short, ?_, ?_, ?_, ?_⟩, hCapacity⟩
  · rw [hHeader 24 (by decide) (by decide)]; exact h.kind
  · rw [hHeader 16 (by decide) (by decide)]; exact h.width
  · rw [hHeader 8 (by decide) (by decide)]; exact h.mask
  · rw [hCapacity]; exact h.capacity
  · rw [hCapacity]; exact hAddress
  · rw [hCapacity]; omega
  · rw [hCapacity]; exact hSeparate

theorem RecordBody.region {heap : Heap} {store : Store Unit} {p : UInt64} {slots : List Slot}
    (h : RecordBody heap store p slots) : heap.Region (block store p) := by
  have := h.below
  have := h.base
  exact ⟨by simp only [block]; omega, h.separate⟩

theorem RecordBody.object {heap : Heap} {store : Store Unit} {p : UInt64} {slots : List Slot}
    (h : RecordBody heap store p slots) : heap.Object store p :=
  ⟨h.base, h.address, h.below, h.separate⟩

/-- A region of positive size apart from a freed object keeps its bytes through the release
and stays a region of the heap after it. -/
theorem Heap.Region.release {heap : Heap} {store : Store Unit} {q : UInt64} {r : Nat × Nat}
    (h : heap.Region r) (hSize : 0 < r.2) (hHeap : heap.At store) (hObject : heap.Object store q)
    (hApart : regionsDisjoint r (block store q)) :
    (heap.release q (store.mem.read64 (q - 32).toUInt32)).Region r ∧
      ∀ a, r.1 ≤ a → a < r.1 + r.2 → (heap.releaseStore store q).mem.bytes a = store.mem.bytes a := by
  have hBase := hObject.base
  have hFit := hObject.address
  simp only [capacityAt] at hFit
  simp only [block, capacityAt] at hApart
  refine ⟨⟨h.below, fun node hNode => regionsDisjoint_symm (insertFree_apart (by omega) (by omega)
    hHeap.free_bounds hSize hApart (fun n hn => regionsDisjoint_symm (h.separate n hn)) node
      hNode)⟩, fun a hLow hHigh => ?_⟩
  refine Heap.releaseStore_bytes hHeap (by omega) (by omega)
    (by unfold regionsDisjoint at hApart; omega) fun node hn => ?_
  have hSep := h.separate node hn
  have := (hHeap.freeList.mem_bounds hn).1
  simp only [regionsDisjoint, FreeNode.region] at hSep
  omega

/-- Releasing an object keeps every region apart from its block. -/
theorem Heap.Keeps.release {heap : Heap} {store : Store Unit} {q : UInt64} (hHeap : heap.At store)
    (hObject : heap.Object store q) :
    heap.Keeps store [block store q] (heap.release q (store.mem.read64 (q - 32).toUInt32))
      (heap.releaseStore store q) [] := fun r hr hpos hApart => by
  obtain ⟨hRegion, hBytes⟩ := hr.release hpos hHeap hObject (hApart _ (List.mem_singleton_self _))
  exact ⟨hBytes, hRegion, fun _ hb => nomatch hb⟩

/-- The allocator invariant holds in any store with the same globals and pages and the same
bytes in the headers of the free blocks. -/
theorem Heap.At.frame {heap : Heap} {store store' : Store Unit} (h : heap.At store)
    (hGlobals : store'.globals = store.globals) (hPages : store'.mem.pages = store.mem.pages)
    (hBytes : ∀ node ∈ heap.free, ∀ a, node.root.toNat - 48 ≤ a → a < node.root.toNat →
      store'.mem.bytes a = store.mem.bytes a) : heap.At store' :=
  ⟨by rw [hGlobals]; exact h.globals, FreeListMemory.frame_headers h.freeList hPages.ge hBytes,
    h.base, by rw [hPages]; exact h.top, by rw [hPages]; exact h.pages, h.above, h.below⟩

theorem PendingAt.frame {mem mem' : Mem} :
    ∀ {head : UInt64} {items : List (UInt64 × List Slot)}, PendingAt mem head items →
      (∀ k ∈ items, mem'.read64 (UInt32.ofNat (k.1.toNat - 40)) =
        mem.read64 (UInt32.ofNat (k.1.toNat - 40))) →
      PendingAt mem' head items
  | _, [], h, _ => h
  | _, (p, _) :: rest, ⟨hHead, hRest⟩, hReads => by
      refine ⟨hHead, ?_⟩
      rw [hReads (p, _) List.mem_cons_self]
      exact PendingAt.frame hRest fun k hk => hReads k (List.mem_cons_of_mem _ hk)

/-- Linking children onto a pending list puts them in front of it in reverse order, when the
count words of the children and of the list lie apart. -/
theorem linkChildren_chain :
    ∀ (mem : Mem) (pending : UInt64) (kids rest : List (UInt64 × List Slot)),
      PendingAt mem pending rest →
      (∀ k ∈ kids ++ rest, 40 ≤ k.1.toNat ∧ k.1.toNat < 4294967296) →
      ((kids ++ rest).map fun k => (k.1.toNat - 40, 8)).Pairwise regionsDisjoint →
      PendingAt (linkChildren mem pending kids).1 (linkChildren mem pending kids).2
        (kids.reverse ++ rest)
  | _, _, [], _, h, _, _ => h
  | mem, pending, (c, cs) :: ks, rest, hRest, hBounds, hPair => by
      simp only [List.cons_append, List.map_cons, List.pairwise_cons] at hBounds hPair
      have hc := hBounds (c, cs) List.mem_cons_self
      simp only at hc
      have hWrite : ∀ k ∈ rest, (mem.write64 (UInt32.ofNat (c.toNat - 40)) pending).read64
          (UInt32.ofNat (k.1.toNat - 40)) = mem.read64 (UInt32.ofNat (k.1.toNat - 40)) :=
        fun k hk => by
          have hk' := hBounds k (List.mem_cons_of_mem _ (List.mem_append_right _ hk))
          have hd := hPair.1 _ (List.mem_map_of_mem (List.mem_append_right _ hk))
          simp only [regionsDisjoint] at hd
          refine Memory.read64_write64_disjoint _ _ _ _ ?_
          rw [UInt32.toNat_ofNat', UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_of_lt (by omega)]
          omega
      have h := linkChildren_chain (mem.write64 (UInt32.ofNat (c.toNat - 40)) pending) c ks
        ((c, cs) :: rest) ⟨rfl, by rw [Memory.read64_write64]; exact hRest.frame hWrite⟩
        (fun k hk => by
          rcases List.mem_append.mp hk with hk | hk
          · exact hBounds k (List.mem_cons_of_mem _ (List.mem_append_left _ hk))
          · rcases List.mem_cons.mp hk with rfl | hk
            · exact hc
            · exact hBounds k (List.mem_cons_of_mem _ (List.mem_append_right _ hk)))
        (by
          have hPerm : List.Perm ((ks ++ (c, cs) :: rest).map (fun k => (k.1.toNat - 40, 8)))
              ((c.toNat - 40, 8) :: (ks ++ rest).map (fun k => (k.1.toNat - 40, 8))) := by
            simp only [List.map_append, List.map_cons]
            exact List.perm_middle
          exact (hPerm.pairwise_iff fun h => regionsDisjoint_symm h).mpr
            (List.pairwise_cons.mpr hPair))
      simpa [linkChildren, List.reverse_cons, List.append_assoc] using h

theorem pairwise_of_ne {α : Type} {R : α → α → Prop} (hSymm : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: xs, h, a, b, ha, hb, hne => by
      rw [List.pairwise_cons] at h
      rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hne
      · subst ha'
        exact h.1 b hb'
      · subst hb'
        exact hSymm _ _ (h.1 a ha')
      · exact pairwise_of_ne hSymm h.2 ha' hb' hne

theorem forestBlocks_cons (store : Store Unit) (q : UInt64) (slots : List Slot)
    (rest : List (UInt64 × List Slot)) :
    forestBlocks store ((q, slots) :: rest) = block store q ::
      (forestBlocks store (childRecords store.mem q 0 slots) ++ forestBlocks store rest) := by
  rw [forestBlocks, List.flatMap_cons, Node.blocks, slotsBlocks_childRecords]
  rfl

theorem forestBlocks_append (store : Store Unit) (a b : List (UInt64 × List Slot)) :
    forestBlocks store (a ++ b) = forestBlocks store a ++ forestBlocks store b :=
  List.flatMap_append

theorem Heap.Region.sub {heap : Heap} {r r' : Nat × Nat} (h : heap.Region r)
    (hSub : regionSub r' r) : heap.Region r' := by
  unfold regionSub at hSub
  have := h.below
  exact ⟨by omega, fun node hNode => by
    have := h.separate node hNode
    unfold regionsDisjoint at this ⊢
    omega⟩

theorem forestBlocks_regions {heap : Heap} {store : Store Unit}
    {items : List (UInt64 × List Slot)}
    (h : ∀ k ∈ items, RecordBody heap store k.1 k.2 ∧ SlotsOwned heap store k.1 0 k.2) :
    ∀ b ∈ forestBlocks store items, heap.Region b := by
  intro b hb
  obtain ⟨k, hk, hb⟩ := List.mem_flatMap.mp hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact (h k hk).1.region
  · exact SlotsOwned.regions k.1 0 k.2 (h k hk).2 b hb

/-- The state of `release`'s pending loop while it frees a tree whose blocks were `tree`,
starting from `heap0` and `initial`: the allocator invariant; the pending records `items`,
linked from `pending`, each with its subtree owned; their blocks pairwise disjoint; every
region of `heap0` of positive size apart from the tree keeping its bytes, staying a region,
and lying apart from the pending blocks; and the same memory caps. -/
structure Releasing (heap0 : Heap) (initial : Store Unit) (tree : List (Nat × Nat)) (heap : Heap)
    (store : Store Unit) (pending : UInt64) (items : List (UInt64 × List Slot)) : Prop where
  at_ : heap.At store
  chain : PendingAt store.mem pending items
  records : ∀ k ∈ items, RecordBody heap store k.1 k.2 ∧ SlotsOwned heap store k.1 0 k.2
  disjoint : (forestBlocks store items).Pairwise regionsDisjoint
  region : ∀ r, heap0.Region r → 0 < r.2 → (∀ b ∈ tree, regionsDisjoint r b) →
    (∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a) ∧ heap.Region r ∧
      ∀ b ∈ forestBlocks store items, regionsDisjoint r b
  caps : store.memoryCaps = initial.memoryCaps

theorem mem_blocks_record (store : Store Unit) (k : UInt64 × List Slot) :
    block store k.1 ∈ Node.blocks store k.1 (.record k.2) := by
  simp [Node.blocks]

theorem toUInt32_sub_ofNat {p k : UInt64} (hk : k.toNat ≤ 48) (hBase : 48 ≤ p.toNat)
    (hFit : p.toNat < 4294967296) : (p - k).toUInt32 = UInt32.ofNat (p.toNat - k.toNat) := by
  rw [Memory.toUInt32_eq_ofNat, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega),
    Nat.mod_eq_of_lt (by omega)]

/-- An owned record carries the header facts that `dropReference` reads. -/
theorem RecordHeader.childHeader {heap : Heap} {store : Store Unit} {c : UInt64}
    {cs : List Slot} (h : RecordHeader heap store c cs) (hHeap : heap.At store) :
    ChildHeader store c := by
  have hBase := h.base
  have hFit := h.address
  have hBelow := h.below
  have hTop := hHeap.top
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · have := h.magic
    rw [toUInt32_sub_ofNat (by decide) (by omega) (by omega)] at this
    exact this
  · have := h.count
    rw [toUInt32_sub_ofNat (by decide) (by omega) (by omega)] at this
    exact this

/-- The block facts of the head of the pending list: its block lies apart from every other
pending block, and the subtrees of its children form disjoint groups. -/
theorem Releasing.groups {heap0 heap : Heap} {initial store : Store Unit}
    {tree : List (Nat × Nat)} {pending q : UInt64} {slots : List Slot}
    {rest : List (UInt64 × List Slot)}
    (h : Releasing heap0 initial tree heap store pending ((q, slots) :: rest)) :
    (∀ b ∈ forestBlocks store (childRecords store.mem q 0 slots) ++ forestBlocks store rest,
      regionsDisjoint (block store q) b) ∧
    (∀ x ∈ forestBlocks store (childRecords store.mem q 0 slots), ∀ y ∈ forestBlocks store rest,
      regionsDisjoint x y) ∧
    (∀ k ∈ childRecords store.mem q 0 slots,
      (Node.blocks store k.1 (.record k.2)).Pairwise regionsDisjoint) ∧
    (childRecords store.mem q 0 slots).Pairwise (fun a b => ∀ x ∈ Node.blocks store a.1 (.record a.2),
      ∀ y ∈ Node.blocks store b.1 (.record b.2), regionsDisjoint x y) ∧
    (forestBlocks store rest).Pairwise regionsDisjoint := by
  have hTop := h.disjoint
  rw [forestBlocks_cons, List.pairwise_cons, List.pairwise_append] at hTop
  obtain ⟨hHead, hKids, hRest, hCross⟩ := hTop
  rw [forestBlocks, List.pairwise_flatMap] at hKids
  exact ⟨hHead, hCross, hKids.1, hKids.2, hRest⟩

theorem Releasing.dropFacts {heap0 heap : Heap} {initial store : Store Unit}
    {tree : List (Nat × Nat)} {pending q : UInt64} {slots : List Slot}
    {rest : List (UInt64 × List Slot)}
    (h : Releasing heap0 initial tree heap store pending ((q, slots) :: rest)) :
    pending = q ∧ 48 ≤ q.toNat ∧ slots.length ≤ 64 ∧
      q.toNat + 8 * slots.length < 4294967296 ∧
      q.toNat + 8 * slots.length ≤ store.mem.pages * 65536 ∧
      store.mem.read64 (q - 8).toUInt32 = maskOf slots ∧
      store.mem.read64 (q - 24).toUInt32 = 1 ∧
      store.mem.read64 (q - 16).toUInt32 = UInt64.ofNat slots.length ∧
      (∀ i (hi : i < slots.length), slots[i] = .child .null →
        store.mem.read64 (slotAddress q i) = 0) ∧
      (∀ k ∈ childRecords store.mem q 0 slots, ChildHeader store k.1) ∧
      ((childRecords store.mem q 0 slots).map fun k => (k.1.toNat - 48, 48)).Pairwise
        regionsDisjoint ∧
      (∀ k ∈ childRecords store.mem q 0 slots,
        regionsDisjoint (k.1.toNat - 48, 48) (q.toNat, 8 * slots.length)) := by
  obtain ⟨hHead, -, -, hGroups, -⟩ := h.groups
  have hq := h.records (q, slots) List.mem_cons_self
  simp only at hq
  obtain ⟨hBody, hSlots⟩ := hq
  have hKidOwned := SlotsOwned.childRecords 0 slots hSlots
  have hCap := hBody.capacity
  have hFit := hBody.address
  have hBelow := hBody.below
  have hTop := h.at_.top
  refine ⟨h.chain.1, by have := hBody.base; omega, hBody.short, by omega, by omega, hBody.mask,
    hBody.kind, hBody.width, fun i hi hNull => by simpa using SlotsOwned.null 0 slots hSlots i hi hNull,
    fun k hk => (hKidOwned k hk).1.childHeader h.at_, ?_, fun k hk => ?_⟩
  · rw [List.pairwise_map]
    refine hGroups.imp_of_mem fun {a b} ha hb hab => ?_
    have hd := hab _ (mem_blocks_record store a) _ (mem_blocks_record store b)
    have := (hKidOwned a ha).1.base
    have := (hKidOwned b hb).1.base
    simp only [block, regionsDisjoint] at hd ⊢
    omega
  · have hd := hHead _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨k, hk,
      mem_blocks_record store k⟩))
    have := (hKidOwned k hk).1.base
    simp only [block, regionsDisjoint] at hd ⊢
    omega

mutual
theorem Node.blocks_size (store : Store Unit) :
    ∀ (p : UInt64) (n : Node), ∀ b ∈ n.blocks store p, 48 ≤ b.2
  | _, .null, _, hb => nomatch hb
  | p, .record slots, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · simp [block]
      · exact slotsBlocks_size store p 0 slots b hb

theorem slotsBlocks_size (store : Store Unit) :
    ∀ (p : UInt64) (i : Nat) (slots : List Slot), ∀ b ∈ slotsBlocks store p i slots, 48 ≤ b.2
  | _, _, [], _, hb => nomatch hb
  | p, i, .word _ :: rest, b, hb => slotsBlocks_size store p (i + 1) rest b hb
  | p, i, .child n :: rest, b, hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact Node.blocks_size store _ n b hb
      · exact slotsBlocks_size store p (i + 1) rest b hb
end

theorem forestBlocks_congr {store store' : Store Unit} :
    ∀ {items : List (UInt64 × List Slot)},
      (∀ k ∈ items, Node.blocks store' k.1 (.record k.2) = Node.blocks store k.1 (.record k.2)) →
      forestBlocks store' items = forestBlocks store items
  | [], _ => rfl
  | k :: ks, h => by
      have hRest := forestBlocks_congr (store := store) (store' := store') (items := ks)
        fun k' hk' => h k' (List.mem_cons_of_mem _ hk')
      simp only [forestBlocks, List.flatMap_cons] at hRest ⊢
      rw [h k List.mem_cons_self, hRest]

theorem forestRecords_append (a b : List (UInt64 × List Slot)) :
    forestRecords (a ++ b) = forestRecords a + forestRecords b := by
  simp [forestRecords]

theorem forestRecords_reverse (a : List (UInt64 × List Slot)) :
    forestRecords a.reverse = forestRecords a := by
  simp [forestRecords, List.sum_reverse]

theorem Releasing.next {heap0 heap : Heap} {initial store : Store Unit}
    {tree : List (Nat × Nat)} {pending q : UInt64} {slots : List Slot}
    {rest : List (UInt64 × List Slot)}
    (h : Releasing heap0 initial tree heap store pending ((q, slots) :: rest)) :
    let next := store.mem.read64 (UInt32.ofNat (q.toNat - 40))
    let kids := childRecords store.mem q 0 slots
    let store1 : Store Unit := { store with mem := (linkChildren store.mem next kids).1 }
    heap.At store1 ∧ heap.Object store1 q ∧
      Releasing heap0 initial tree (heap.release q (store1.mem.read64 (q - 32).toUInt32))
        (heap.releaseStore store1 q) (linkChildren store.mem next kids).2 (kids.reverse ++ rest) ∧
      forestRecords (kids.reverse ++ rest) < forestRecords ((q, slots) :: rest) := by
  intro next kids store1
  have hTop := h.disjoint
  rw [forestBlocks_cons, List.pairwise_cons, ← forestBlocks_append] at hTop
  obtain ⟨hQApart, hTail⟩ := hTop
  have hTail' := hTail
  rw [forestBlocks, List.pairwise_flatMap] at hTail'
  obtain ⟨hWithin, hGroups⟩ := hTail'
  have hq := h.records (q, slots) List.mem_cons_self
  simp only at hq
  obtain ⟨hBody, hSlots⟩ := hq
  have hKidOwned : ∀ k ∈ kids, RecordHeader heap store k.1 k.2 ∧ SlotsOwned heap store k.1 0 k.2 :=
    SlotsOwned.childRecords 0 slots hSlots
  have hItem : ∀ k ∈ kids ++ rest,
      RecordBody heap store k.1 k.2 ∧ SlotsOwned heap store k.1 0 k.2 := fun k hk => by
    rcases List.mem_append.mp hk with hk | hk
    · exact ⟨(hKidOwned k hk).1.body, (hKidOwned k hk).2⟩
    · exact h.records k (List.mem_cons_of_mem _ hk)
  have hBlockMem : ∀ k ∈ kids ++ rest, block store k.1 ∈ forestBlocks store (kids ++ rest) :=
    fun k hk => List.mem_flatMap.mpr ⟨k, hk, mem_blocks_record store k⟩
  have hSymm : ∀ a b : UInt64 × List Slot,
      (∀ x ∈ Node.blocks store a.1 (.record a.2), ∀ y ∈ Node.blocks store b.1 (.record b.2),
        regionsDisjoint x y) →
      (∀ x ∈ Node.blocks store b.1 (.record b.2), ∀ y ∈ Node.blocks store a.1 (.record a.2),
        regionsDisjoint x y) :=
    fun a b hab x hx y hy => regionsDisjoint_symm (hab y hy x hx)
  have hCountSub : ∀ k ∈ kids ++ rest, regionSub (k.1.toNat - 40, 8) (block store k.1) :=
    fun k hk => by
      have := (hItem k hk).1.base
      simp only [regionSub, block]
      omega
  -- A block of record `k` lies apart from the count word of every other kid.
  have hOther : ∀ k ∈ kids ++ rest, ∀ k' ∈ kids, k' ≠ k →
      ∀ x ∈ Node.blocks store k.1 (.record k.2), regionsDisjoint x (k'.1.toNat - 40, 8) :=
    fun k hk k' hk' hne x hx => regionsDisjoint_symm (regionsDisjoint_of_sub
      (hCountSub k' (List.mem_append_left _ hk'))
      (pairwise_of_ne hSymm hGroups (List.mem_append_left _ hk') hk hne _
        (mem_blocks_record store k') x hx))
  have hLinkBytes : ∀ R : Nat × Nat, (∀ k ∈ kids, regionsDisjoint R (k.1.toNat - 40, 8)) →
      ∀ a, R.1 ≤ a → a < R.1 + R.2 → store1.mem.bytes a = store.mem.bytes a :=
    fun R hR a hLow hHigh => linkChildren_bytes store.mem next a kids fun k hk => by
      have := (hKidOwned k hk).1.base
      have := (hKidOwned k hk).1.address
      have hd := hR k hk
      unfold regionsDisjoint at hd
      exact ⟨by omega, by omega, by omega⟩
  have hAt1 : heap.At store1 := Heap.At.frame h.at_ rfl (linkChildren_pages _ _ _)
    fun node hNode a hLow hHigh => by
      have := h.at_.above node hNode
      refine hLinkBytes (node.root.toNat - 48, 48) (fun k hk => ?_) a hLow (by simp; omega)
      have hSep := (hKidOwned k hk).1.separate node hNode
      have := (hKidOwned k hk).1.base
      simp only [regionsDisjoint, FreeNode.region] at hSep ⊢
      omega
  have hQKids : ∀ k ∈ kids, regionsDisjoint (block store q) (k.1.toNat - 40, 8) := fun k hk =>
    regionsDisjoint_symm (regionsDisjoint_of_sub (hCountSub k (List.mem_append_left _ hk))
      (regionsDisjoint_symm (hQApart _ (hBlockMem k (List.mem_append_left _ hk)))))
  have hBaseQ := hBody.base
  have hFitQ := hBody.address
  have hCap1 : capacityAt store1 q = capacityAt store q := by
    unfold capacityAt
    congr 1
    refine Memory.read64_congr _ fun i hi => ?_
    rw [headerAddress_toNat (by simp; omega) (by omega)]
    exact hLinkBytes _ hQKids _ (by simp [block]; omega) (by simp [block]; omega)
  have hObj1 : heap.Object store1 q :=
    ⟨hBaseQ, by rw [hCap1]; exact hFitQ, by rw [hCap1]; exact hBody.below,
      by rw [hCap1]; exact hBody.separate⟩
  have hBlockQ1 : block store1 q = block store q := block_eq hCap1
  refine ⟨hAt1, hObj1, ?_, ?_⟩
  swap
  · rw [forestRecords_append, forestRecords_reverse]
    change forestRecords (childRecords store.mem q 0 slots) + forestRecords rest < _
    have hHead : forestRecords ((q, slots) :: rest) = 1 + slotsRecords slots + forestRecords rest := by
      simp [forestRecords, Node.records]
    rw [hHead, slotsRecords_childRecords store.mem q 0 slots]
    omega
  have hRel : ∀ R, heap.Region R → 0 < R.2 → regionsDisjoint R (block store q) →
      (heap.release q (store1.mem.read64 (q - 32).toUInt32)).Region R ∧
        ∀ a, R.1 ≤ a → a < R.1 + R.2 →
          (heap.releaseStore store1 q).mem.bytes a = store1.mem.bytes a :=
    fun R hR hSize hD => Heap.Region.release hR hSize hAt1 hObj1 (by rw [hBlockQ1]; exact hD)
  have hBoth : ∀ R, heap.Region R → 0 < R.2 → regionsDisjoint R (block store q) →
      (∀ k ∈ kids, regionsDisjoint R (k.1.toNat - 40, 8)) →
      (heap.release q (store1.mem.read64 (q - 32).toUInt32)).Region R ∧
        ∀ a, R.1 ≤ a → a < R.1 + R.2 →
          (heap.releaseStore store1 q).mem.bytes a = store.mem.bytes a :=
    fun R hR hSize hD hK => ⟨(hRel R hR hSize hD).1, fun a hl hh =>
      ((hRel R hR hSize hD).2 a hl hh).trans (hLinkBytes R hK a hl hh)⟩
  have hFrame : ∀ k ∈ kids ++ rest,
      (RecordBody (heap.release q (store1.mem.read64 (q - 32).toUInt32))
          (heap.releaseStore store1 q) k.1 k.2 ∧
        SlotsOwned (heap.release q (store1.mem.read64 (q - 32).toUInt32))
          (heap.releaseStore store1 q) k.1 0 k.2) ∧
      Node.blocks (heap.releaseStore store1 q) k.1 (.record k.2) =
        Node.blocks store k.1 (.record k.2) := fun k hk => by
    obtain ⟨hB, hS⟩ := hItem k hk
    have hBase := hB.base
    have hFit := hB.address
    have hCap := hB.capacity
    have hRegK := hB.region
    have hQk := hQApart _ (hBlockMem k hk)
    have hR : heap.Region (k.1.toNat - 32, 32 + capacityAt store k.1) :=
      hRegK.sub (by simp only [regionSub, block]; omega)
    have hRK : ∀ k' ∈ kids,
        regionsDisjoint (k.1.toNat - 32, 32 + capacityAt store k.1) (k'.1.toNat - 40, 8) :=
      fun k' hk' => by
        by_cases hEq : k' = k
        · rw [hEq]
          simp only [regionsDisjoint]
          omega
        · exact regionsDisjoint_of_sub (by simp only [regionSub, block]; omega)
            (hOther k hk k' hk' hEq _ (mem_blocks_record store k))
    obtain ⟨-, hBytesR⟩ := hBoth _ hR (by simp)
      (regionsDisjoint_of_sub (by simp only [regionSub, block]; omega) (regionsDisjoint_symm hQk))
      hRK
    obtain ⟨hBody2, hCapEq⟩ := hB.frame
      (fun a hl hh => hBytesR a (by simp only; omega) (by simp only; omega))
      (hRel _ hRegK (by simp [block]) (regionsDisjoint_symm hQk)).1
    obtain ⟨hSlots2, hBlocksEq⟩ := SlotsOwned.frame k.1 0 k.2 hS (by omega)
      (fun a hl hh => hBytesR a (by simp only; omega) (by simp only; omega)) fun b hb => by
        have hbMem : b ∈ Node.blocks store k.1 (.record k.2) := List.mem_cons_of_mem _ hb
        have hRb := SlotsOwned.regions k.1 0 k.2 hS b hb
        have hSize := slotsBlocks_size store k.1 0 k.2 b hb
        have hbQ := hQApart b (List.mem_flatMap.mpr ⟨k, hk, hbMem⟩)
        have hbK : ∀ k' ∈ kids, regionsDisjoint b (k'.1.toNat - 40, 8) := fun k' hk' => by
          by_cases hEq : k' = k
          · have hW := hWithin k hk
            rw [Node.blocks, List.pairwise_cons] at hW
            rw [hEq]
            exact regionsDisjoint_symm (regionsDisjoint_of_sub (hCountSub k hk) (hW.1 b hb))
          · exact hOther k hk k' hk' hEq b hbMem
        obtain ⟨hReg2, hBytes2⟩ := hBoth b hRb (by omega) (regionsDisjoint_symm hbQ) hbK
        exact ⟨hBytes2, hReg2⟩
    refine ⟨⟨hBody2, hSlots2⟩, ?_⟩
    simp only [Node.blocks, block_eq hCapEq, hBlocksEq]
  have hMem : ∀ k ∈ kids.reverse ++ rest, k ∈ kids ++ rest := fun k hk => by
    rcases List.mem_append.mp hk with hk | hk
    · exact List.mem_append_left _ (List.mem_reverse.mp hk)
    · exact List.mem_append_right _ hk
  have hBlocks2 : forestBlocks (heap.releaseStore store1 q) (kids.reverse ++ rest) =
      forestBlocks store (kids.reverse ++ rest) :=
    forestBlocks_congr fun k hk => (hFrame k (hMem k hk)).2
  have hPerm : List.Perm (forestBlocks store (kids.reverse ++ rest))
      (forestBlocks store (kids ++ rest)) := by
    rw [forestBlocks_append, forestBlocks_append]
    exact ((List.reverse_perm kids).flatMap_right _).append_right _
  refine ⟨Heap.At.release hAt1 hObj1, ?_, fun k hk => (hFrame k (hMem k hk)).1, ?_, ?_, ?_⟩
  · have hChain1 := linkChildren_chain store.mem next kids rest h.chain.2
      (fun k hk => by
        have := (hItem k hk).1.base
        have := (hItem k hk).1.address
        exact ⟨by omega, by omega⟩)
      (by
        rw [List.pairwise_map]
        exact hGroups.imp_of_mem fun {a b} ha hb hab => regionsDisjoint_of_sub (hCountSub a ha)
          (regionsDisjoint_symm (regionsDisjoint_of_sub (hCountSub b hb) (regionsDisjoint_symm
            (hab _ (mem_blocks_record store a) _ (mem_blocks_record store b))))))
    refine hChain1.frame fun k hk => Memory.read64_congr _ fun i hi => ?_
    have hk' := hMem k hk
    have hB := (hItem k hk').1
    have := hB.base
    have := hB.address
    have hQk := hQApart _ (hBlockMem k hk')
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    exact (hRel _ hB.region (by simp [block]) (regionsDisjoint_symm hQk)).2 _
      (by simp only [block]; omega) (by simp only [block]; omega)
  · rw [hBlocks2]
    exact (hPerm.pairwise_iff fun h => regionsDisjoint_symm h).mpr hTail
  · intro r hr hSize hTree
    obtain ⟨hBytes0, hReg, hApartF⟩ := h.region r hr hSize hTree
    rw [forestBlocks_cons] at hApartF
    have hApartQ := hApartF _ List.mem_cons_self
    have hApartT : ∀ b ∈ forestBlocks store (kids ++ rest), regionsDisjoint r b := fun b hb =>
      hApartF b (List.mem_cons_of_mem _ (by rw [forestBlocks_append] at hb; exact hb))
    obtain ⟨hReg2, hBytes2⟩ := hBoth r hReg hSize hApartQ fun k hk => regionsDisjoint_symm
      (regionsDisjoint_of_sub (hCountSub k (List.mem_append_left _ hk))
        (regionsDisjoint_symm (hApartT _ (hBlockMem k (List.mem_append_left _ hk)))))
    refine ⟨fun a hl hh => (hBytes2 a hl hh).trans (hBytes0 a hl hh), hReg2, fun b hb => ?_⟩
    rw [hBlocks2] at hb
    exact hApartT b (hPerm.mem_iff.mp hb)
  · exact h.caps

/-- After `release` drops the reference to the root of a tree of owned records, the root is
the one pending record. -/
theorem Releasing.start {heap : Heap} {store : Store Unit} {p : UInt64} {slots : List Slot}
    (hHeap : heap.At store) (hOwned : NodeOwned heap store p (.record slots))
    (hDisjoint : (Node.blocks store p (.record slots)).Pairwise regionsDisjoint) :
    Releasing heap store (Node.blocks store p (.record slots)) heap (releaseEntry store p) p
      [(p, slots)] := by
  obtain ⟨hHeader, hSlots⟩ := hOwned
  have hBase := hHeader.base
  have hFit := hHeader.address
  have hCap := hHeader.capacity
  have hObj : heap.Object store p := ⟨hBase, hFit, hHeader.below, hHeader.separate⟩
  obtain ⟨hAt1, -, -⟩ := hObj.clearCount hHeap
  have hw : (UInt32.ofNat (p.toNat - 40)).toNat = p.toNat - 40 := by
    rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  -- The cleared count word lies in the root's block, apart from everything else.
  have hBytes : ∀ a, (a < p.toNat - 40 ∨ p.toNat - 32 ≤ a) →
      (releaseEntry store p).mem.bytes a = store.mem.bytes a := fun a ha => by
    simp only [releaseEntry]
    exact Memory.write64_bytes_outside _ _ _ (by rw [hw]; omega)
  have hW := hDisjoint
  rw [Node.blocks, List.pairwise_cons] at hW
  have hBlockSub : regionSub (p.toNat - 40, 8) (block store p) := by
    simp only [regionSub, block]
    omega
  have hApart : ∀ b, regionsDisjoint b (block store p) → ∀ a, b.1 ≤ a → a < b.1 + b.2 →
      (releaseEntry store p).mem.bytes a = store.mem.bytes a := fun b hb a hl hh => hBytes a (by
    have := regionsDisjoint_symm (regionsDisjoint_of_sub hBlockSub (regionsDisjoint_symm hb))
    unfold regionsDisjoint at this
    omega)
  obtain ⟨hBody1, hCapEq⟩ := hHeader.body.frame (fun a hl hh => hBytes a (by omega)) hHeader.region
  obtain ⟨hSlots1, hBlocksEq⟩ := SlotsOwned.frame p 0 slots hSlots (by omega)
    (fun a hl hh => hBytes a (by omega)) fun b hb =>
      ⟨hApart b (regionsDisjoint_symm (hW.1 b hb)), SlotsOwned.regions p 0 slots hSlots b hb⟩
  have hTree : forestBlocks (releaseEntry store p) [(p, slots)] = Node.blocks store p (.record slots) := by
    simp only [forestBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil, Node.blocks,
      block_eq hCapEq, hBlocksEq]
  refine ⟨hAt1, ⟨rfl, ?_⟩, fun k hk => ?_, by rw [hTree]; exact hDisjoint, fun r hr hSize hr' => ?_,
    rfl⟩
  · simp only [releaseEntry, PendingAt]
    exact Memory.read64_write64 _ _ _
  · simp only [List.mem_singleton] at hk
    subst hk
    exact ⟨hBody1, hSlots1⟩
  · refine ⟨hApart r (hr' _ (by simp [Node.blocks])), hr, ?_⟩
    rw [hTree]
    exact hr'

/-- When the pending list is empty, `release` has freed the tree. -/
theorem Releasing.done {heap0 heap : Heap} {initial store : Store Unit}
    {tree : List (Nat × Nat)} {pending : UInt64}
    (h : Releasing heap0 initial tree heap store pending []) :
    pending = 0 ∧ heap.At store ∧ store.memoryCaps = initial.memoryCaps ∧
      ∀ r, heap0.Region r → 0 < r.2 → (∀ b ∈ tree, regionsDisjoint r b) →
        (∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a) ∧
          heap.Region r :=
  ⟨h.chain, h.at_, h.caps, fun r hr hSize hTree =>
    ⟨(h.region r hr hSize hTree).1, (h.region r hr hSize hTree).2.1⟩⟩

/-- `release` on the root of a tree of owned records with pairwise disjoint blocks frees the
tree: it returns, the allocator invariant holds for some heap, the memory caps are
unchanged, and every region of positive size of the old heap apart from the tree keeps its
bytes and stays a region.  The null pointer returns at once. -/
theorem release_tree_run {m : Module} {typeIdx : Nat} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (releaseFunction typeIdx)) (env : HostEnv Unit) (heap : Heap)
    (store : Store Unit) (p : UInt64) (n : Node) (hHeap : heap.At store)
    (hOwned : NodeOwned heap store p n) (hDisjoint : (n.blocks store p).Pairwise regionsDisjoint) :
    TerminatesWith env m 1 store [.i64 p] fun final out => out = [] ∧
      ∃ heap' : Heap, heap'.At final ∧ final.memoryCaps = store.memoryCaps ∧
        ∀ r, heap.Region r → 0 < r.2 → (∀ b ∈ n.blocks store p, regionsDisjoint r b) →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  refine TerminatesWith.of_wp_entry_for (f := releaseFunction typeIdx)
    (by simpa [hImports] using hFunc) ?_ (by simp [hImports])
  cases n with
  | null =>
    have hp : p = 0 := hOwned
    subst hp
    simp [releaseFunction, releaseBody, Function.toLocals, Function.numParams, ValueType.zero,
      wp_simp]
    refine wp_iff_cons rfl ?_
    simp [wp_simp]
    exact ⟨heap, hHeap, fun a b hr _ _ => hr⟩
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
    simp [releaseFunction, releaseBody, dropReference, checkMagic, headerLoad, headerStore,
      releaseCount, releasePending, releaseObject, Function.toLocals, Function.numParams,
      ValueType.zero, wp_simp, hPtr]
    refine wp_iff_cons rfl ?_
    have hb48 : p.toNat - 48 + 8 ≤ store.mem.pages * 65536 := by omega
    have hb40 : p.toNat - 40 + 8 ≤ store.mem.pages * 65536 := by omega
    simp [wp_simp, hs48, hm48, hb48, hMagic]
    refine wp_iff_cons rfl ?_
    simp [wp_simp, hs40, hm40, hb40, hCount]
    refine wp_iff_cons rfl ?_
    simp [wp_simp, hs40, hm40, hb40]
    refine wp_block_cons ?_
    refine wp_loop_ghost (fun k st s => ∃ (heap' : Heap) (v : ReleaseVars)
        (items : List (UInt64 × List Slot)), s = v.toLocals ∧ v.root = p ∧
        forestRecords items = k ∧
        Releasing heap store (Node.blocks store p (.record slots)) heap' st v.pending items)
      (forestRecords [(p, slots)])
      ⟨heap, ⟨p, 1, p, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, [(p, slots)], by
        simp [ReleaseVars.toLocals], rfl, rfl,
        Releasing.start hHeap ⟨hHeader, hSlots⟩ hDisjoint⟩ ?_
    rintro k st s ⟨heap', v, items, rfl, hRoot, rfl, hR⟩
    obtain ⟨root, count, pending, object, kind, length, width, mask, element, slot, child,
      previous, current⟩ := v
    simp only at hRoot hR
    subst hRoot
    cases items with
    | nil =>
      obtain ⟨hPending, hAt', hCaps', hFrame'⟩ := hR.done
      subst hPending
      simp [ReleaseVars.toLocals, wp_simp]
      exact ⟨heap', hAt', hCaps', fun a b hr hb hT =>
        hFrame' (a, b) hr hb fun x hx => hT x.1 x.2 hx⟩
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
      simp [ReleaseVars.toLocals, wp_simp, hq0, hqs40, hqm40, hqb40]
      obtain ⟨hAt1, hObj1, hR', hLt⟩ := hR.next
      refine dropChildren_spec env st
        ⟨root, count, st.mem.read64 (UInt32.ofNat (pending.toNat - 40)), pending, kind, length,
          width, mask, element, slot, child, previous, current⟩ qslots hqBase hShort hqAddress
        hqMemory hMaskWord hKindWord hWidthWord hNull hKids hApart hPayload _ _
        fun v' hRoot' hObj' hPend' => ?_
      simp only at hRoot' hObj' hPend'
      refine freeObject_spec env heap' _ v' hAt1 (by rw [hObj']; exact hObj1) _ _
        fun prev cur => ?_
      rw [hObj']
      simp [wp_simp]
      exact ⟨_, v'.atPlace prev cur, _, hLt, ⟨rfl, rfl⟩,
        by simpa [ReleaseVars.atPlace] using hRoot', by
          simp only [ReleaseVars.atPlace]
          rw [hPend']
          exact hR'⟩

end Project.Pipeline
