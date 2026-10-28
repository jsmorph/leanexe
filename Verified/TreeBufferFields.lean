import Verified.TreeHeapFields
import Verified.FieldsMixed
import Verified.TreeNodeArgs

/-! The buffer fields of a record under construction: the facts of a buffer in a record from its
representation and its normalization, the locals and the normal roots of the buffer arguments,
and the blocks of the record's array and buffer slots, which hold the arrays and the buffers in
the order of the fields. -/

namespace Verified

open Wasm LeanExe.Pipeline

theorem ofFn_flatten_cast {α : Type} {n m : Nat} (h : n = m + 1) (f : Fin n → List α) :
    (List.ofFn f).flatten =
      f ⟨0, by omega⟩ ++ (List.ofFn fun i : Fin m => f ⟨i.val + 1, by omega⟩).flatten := by
  subst h
  rw [List.ofFn_succ, List.flatten_cons]
  rfl

/-- A buffer with a normal root, as a record holds it. -/
theorem _root_.LeanExe.Pipeline.Bytes.Rep.recordBuffer
    {heap : Heap} {store : Store Unit} {root length : UInt64}
    {data : LeanExe.Bytes} (h : Bytes.Rep heap store root length data)
    (hNormal : length = 0 → root = 0) : RecordBuffer heap store root length data := by
  refine ⟨?_, ?_⟩
  · by_cases hSize : data.data.size = 0
    · have hZero : length = 0 := UInt64.toNat_inj.mp (by rw [h.length_eq, hSize]; rfl)
      exact .inl ⟨hNormal hZero, hSize⟩
    · rcases h.buffer with ⟨_, hEmpty⟩ | hBuffer
      · exact absurd hEmpty hSize
      · exact .inr ⟨hSize, hBuffer⟩
  · rw [← h.length_eq, UInt64.ofNat_toNat]

/-- The block of a buffer that a record holds is its region. -/
theorem RecordBuffer.blocks {heap : Heap} {store : Store Unit} {root length : UInt64}
    {data : LeanExe.Bytes} (h : RecordBuffer heap store root length data) :
    (bufferRoots data root).map (block store) = Bytes.regions store root := by
  rcases h.1 with ⟨rfl, hEmpty⟩ | ⟨hNonempty, hBuffer⟩
  · simp [bufferRoots, Bytes.regions, hEmpty]
  · simp [bufferRoots, Bytes.regions, hNonempty, hBuffer.nonzero]

/-- The blocks of the arrays and the nonempty buffers among `fields`, the arrays first. -/
theorem heapFieldBlocks_perm (store : Store Unit) {heap : Heap} (fields : List TreeField) :
    ∀ pointers words roots lengths buffers,
      (∀ i, RecordBuffer heap store (roots i) (lengths i) (buffers i)) →
      (fieldBlocks store (heapValues fields pointers roots lengths)
        (heapSlots fields words buffers)).Perm
        ((List.ofFn fun i => [block store (pointers i)]).flatten ++
          (List.ofFn fun i => Bytes.regions store (roots i)).flatten) := by
  induction fields with
  | nil => intros; simp [heapValues, heapSlots, fieldBlocks]
  | cons field rest ih =>
    intro pointers words roots lengths buffers hBuffers
    cases field with
    | word e => exact ih _ _ _ _ _ (fun i => hBuffers _)
    | child => exact ih _ _ _ _ _ (fun i => hBuffers _)
    | array e =>
      simp only [heapValues, heapSlots, fieldBlocks, Slot.valueBlocks, List.singleton_append]
      rw [ofFn_flatten_cast (m := (rest.filterMap TreeField.arrayElem?).length)
        (by simp [TreeField.arrayElem?]) (fun i => [block store (pointers i)])]
      exact (ih _ _ _ _ _ (fun i => hBuffers _)).cons _
    | bytes =>
      simp only [heapValues, heapSlots, fieldBlocks, Slot.valueBlocks, List.nil_append]
      rw [(hBuffers ⟨0, by simp⟩).blocks,
        ofFn_flatten_cast (m := rest.count .bytes) (by simp)
          (fun i => Bytes.regions store (roots i))]
      have hRest := ih (fun i => pointers ⟨i.val, by
          simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
        (fun i => words ⟨i.val, by
          simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
        (fun i => roots ⟨i.val + 1, by simp⟩) (fun i => lengths ⟨i.val + 1, by simp⟩)
        (fun i => buffers ⟨i.val + 1, by simp⟩) (fun i => hBuffers _)
      refine (hRest.append_left _).trans ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _

/-- The arguments' normal words, after a prefix of the arguments. -/
theorem FieldsNormal.drop_prefix {qs : List Ty} :
    (ps : List Ty) → (first rest : List Value) → first.length = (ps.map Ty.width).sum →
      FieldsNormal (ps ++ qs) (first ++ rest) → FieldsNormal qs rest
  | [], first, rest, hLength, h => by
    have hNil : first = [] := List.length_eq_zero_iff.mp (by simpa using hLength)
    subst hNil
    simpa using h
  | p :: ps, first, rest, hLength, h => by
    simp only [List.map_cons, List.sum_cons] at hLength
    have hDrop : (first ++ rest).drop p.width = first.drop p.width ++ rest :=
      List.drop_append_of_le_length (by omega)
    have hTail := h.2
    rw [hDrop] at hTail
    exact FieldsNormal.drop_prefix ps (first.drop p.width) rest
      (by rw [List.length_drop]; omega) hTail

/-- The normal roots of buffer arguments: each empty buffer has root 0. -/
theorem FieldsNormal.bytesFields {ps : List Ty} :
    (n : Nat) → (roots lengths : Fin n → UInt64) → (rest : List Value) →
      FieldsNormal (List.replicate n .bytes ++ ps)
        ((List.ofFn fun i => [Value.i64 (roots i), .i64 (lengths i)]).flatten ++ rest) →
      ∀ i, lengths i = 0 → roots i = 0
  | 0, _, _, _, _, i => Fin.elim0 i
  | n + 1, roots, lengths, rest, h, i => by
    rw [List.ofFn_succ, List.flatten_cons] at h
    obtain ⟨hFirst, hRest⟩ := h
    have hTake : ([Value.i64 (roots 0), .i64 (lengths 0)] ++
        (List.ofFn fun i : Fin n =>
          [Value.i64 (roots i.succ), .i64 (lengths i.succ)]).flatten ++ rest).take 2 =
        [.i64 (roots 0), .i64 (lengths 0)] := by simp
    have hDrop : ([Value.i64 (roots 0), .i64 (lengths 0)] ++
        (List.ofFn fun i : Fin n =>
          [Value.i64 (roots i.succ), .i64 (lengths i.succ)]).flatten ++ rest).drop 2 =
        (List.ofFn fun i : Fin n =>
          [Value.i64 (roots i.succ), .i64 (lengths i.succ)]).flatten ++ rest := by simp
    change Ty.Normal .bytes (List.take 2 _) at hFirst
    change FieldsNormal _ (List.drop 2 _) at hRest
    rw [hTake] at hFirst
    rw [hDrop] at hRest
    cases i using Fin.cases with
    | zero =>
      intro hZero
      have := hFirst.1 (by rw [hZero])
      simpa using this
    | succ i =>
      exact FieldsNormal.bytesFields n (fun i => roots i.succ) (fun i => lengths i.succ) rest
        hRest i

/-- The locals of buffer arguments hold their roots and lengths. -/
theorem LocalsHold.ofFn_pairs {s : Locals} :
    (n : Nat) → (loc : Nat) → (roots lengths : Fin n → UInt64) →
    LocalsHold s loc (List.replicate (2 * n) .i64)
      (List.ofFn fun i => [Value.i64 (roots i), .i64 (lengths i)]).flatten →
    ∀ i, s.get (loc + 2 * i.val) = some (.i64 (roots i)) ∧
      s.get (loc + 2 * i.val + 1) = some (.i64 (lengths i))
  | 0, _, _, _, _, i => Fin.elim0 i
  | n + 1, loc, roots, lengths, h, i => by
    have hTypes : List.replicate (2 * (n + 1)) ValueType.i64 =
        [.i64, .i64] ++ List.replicate (2 * n) .i64 := by
      rw [show 2 * (n + 1) = 2 + 2 * n by omega, List.replicate_add]
      rfl
    rw [hTypes, List.ofFn_succ, List.flatten_cons] at h
    obtain ⟨hFirst, hRest⟩ := (LocalsHold.append (by rfl)).mp h
    cases i using Fin.cases with
    | zero =>
      have h0 := hFirst 0 (by simp)
      have h1 := hFirst 1 (by simp)
      simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero]
      exact ⟨by simpa [slotIndex] using h0, by simpa [slotIndex] using h1⟩
    | succ i =>
      have hTail := LocalsHold.ofFn_pairs n (loc + 2) (fun i => roots i.succ)
        (fun i => lengths i.succ) (by simpa using hRest) i
      have e1 : loc + 2 * (i.val + 1) = loc + 2 + 2 * i.val := by omega
      simp only [Fin.val_succ]
      rw [e1]
      exact hTail

/-- The blocks of the array and buffer slots from slot `start` on of the record at `p`, the
arrays first: each array's block and each nonempty buffer's block, at the addresses that the
slots hold. -/
theorem heapSlots_blocks_perm (store : Store Unit) (p : UInt64) (fields : List TreeField) :
    ∀ start arrays buffers,
      (slotsBlocks store p start (heapSlots fields arrays buffers)).Perm
        ((List.ofFn fun i => [block store
          (store.mem.read64 (slotAddress p (start + heapArraySlot fields i)))]).flatten ++
        (List.ofFn fun i => (bufferRoots (buffers i)
          (store.mem.read64 (slotAddress p (start + heapBufferSlot fields i)))).map
            (block store)).flatten) := by
  induction fields with
  | nil => intros; simp [heapSlots, slotsBlocks]
  | cons field rest ih =>
    intro start arrays buffers
    cases field with
    | word e => exact ih _ _ _
    | child => exact ih _ _ _
    | array e =>
      simp only [heapSlots, slotsBlocks]
      rw [ofFn_flatten_cast (m := (rest.filterMap TreeField.arrayElem?).length)
        (by simp [TreeField.arrayElem?]) (fun i => [block store
          (store.mem.read64 (slotAddress p (start + heapArraySlot (.array e :: rest) i)))])]
      simp only [heapArraySlot, heapBufferSlot, Nat.succ_ne_zero, ↓reduceDIte,
        Nat.add_sub_cancel, Nat.add_zero, List.singleton_append]
      have hIH := ih (start + 1) (fun i => arrays ⟨i.val + 1, by simp [TreeField.arrayElem?]⟩)
        (fun i => buffers ⟨i.val, by simpa using i.isLt⟩)
      have e : ∀ x, start + 1 + x = start + (x + 1) := fun x => by omega
      simp only [e] at hIH
      exact hIH.cons _
    | bytes =>
      simp only [heapSlots, slotsBlocks, List.nil_append]
      rw [ofFn_flatten_cast (m := rest.count .bytes) (by simp)
        (fun i => (bufferRoots (buffers i) (store.mem.read64
          (slotAddress p (start + heapBufferSlot (.bytes :: rest) i)))).map (block store))]
      simp only [heapArraySlot, heapBufferSlot, Nat.succ_ne_zero, ↓reduceDIte,
        Nat.add_sub_cancel, Nat.add_zero]
      have hIH := ih (start + 1 + 1) (fun i => arrays ⟨i.val, by
          simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
        (fun i => buffers ⟨i.val + 1, by simp⟩)
      have e : ∀ x, start + 1 + 1 + x = start + (x + 2) := fun x => by omega
      simp only [e] at hIH
      refine (hIH.append_left _).trans ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _

/-- The regions of the array and buffer slots from slot `start` on of the record at `p`, the
arrays first: each array's length word and elements and each nonempty buffer's block, at the
addresses that the slots hold. -/
theorem heapSlots_regions_perm (store : Store Unit) (p : UInt64) (fields : List TreeField) :
    ∀ start arrays buffers,
      (slotsRegions store p start (heapSlots fields arrays buffers)).Perm
        ((List.ofFn fun i => [((store.mem.read64
          (slotAddress p (start + heapArraySlot fields i))).toNat,
            8 * ((arrays i).size + 1))]).flatten ++
        (List.ofFn fun i => (bufferRoots (buffers i)
          (store.mem.read64 (slotAddress p (start + heapBufferSlot fields i)))).map
            (block store)).flatten) := by
  induction fields with
  | nil => intros; simp [heapSlots, slotsRegions]
  | cons field rest ih =>
    intro start arrays buffers
    cases field with
    | word e => exact ih _ _ _
    | child => exact ih _ _ _
    | array e =>
      simp only [heapSlots, slotsRegions]
      rw [ofFn_flatten_cast (m := (rest.filterMap TreeField.arrayElem?).length)
        (by simp [TreeField.arrayElem?]) (fun i => [((store.mem.read64
          (slotAddress p (start + heapArraySlot (.array e :: rest) i))).toNat,
            8 * ((arrays i).size + 1))])]
      simp only [heapArraySlot, heapBufferSlot, Nat.succ_ne_zero, ↓reduceDIte,
        Nat.add_sub_cancel, Nat.add_zero, List.singleton_append]
      have hIH := ih (start + 1) (fun i => arrays ⟨i.val + 1, by simp [TreeField.arrayElem?]⟩)
        (fun i => buffers ⟨i.val, by simpa using i.isLt⟩)
      have e : ∀ x, start + 1 + x = start + (x + 1) := fun x => by omega
      simp only [e] at hIH
      exact hIH.cons _
    | bytes =>
      simp only [heapSlots, slotsRegions, List.nil_append]
      rw [ofFn_flatten_cast (m := rest.count .bytes) (by simp)
        (fun i => (bufferRoots (buffers i) (store.mem.read64
          (slotAddress p (start + heapBufferSlot (.bytes :: rest) i)))).map (block store))]
      simp only [heapArraySlot, heapBufferSlot, Nat.succ_ne_zero, ↓reduceDIte,
        Nat.add_sub_cancel, Nat.add_zero]
      have hIH := ih (start + 1 + 1) (fun i => arrays ⟨i.val, by
          simp only [List.filterMap_cons, TreeField.arrayElem?]; exact i.isLt⟩)
        (fun i => buffers ⟨i.val + 1, by simp⟩)
      have e : ∀ x, start + 1 + 1 + x = start + (x + 2) := fun x => by omega
      simp only [e] at hIH
      refine (hIH.append_left _).trans ?_
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_append_comm.append_right _

#print axioms heapSlots_blocks_perm
#print axioms heapSlots_regions_perm
/-- Locals that hold the roots and lengths of buffers hold their words. -/
theorem LocalsHold.ofFn_pairs_of {s : Locals} :
    (n : Nat) → (loc : Nat) → (roots lengths : Fin n → UInt64) →
    (∀ i, s.get (loc + 2 * i.val) = some (.i64 (roots i)) ∧
      s.get (loc + 2 * i.val + 1) = some (.i64 (lengths i))) →
    LocalsHold s loc (List.replicate (2 * n) .i64)
      (List.ofFn fun i => [Value.i64 (roots i), .i64 (lengths i)]).flatten
  | 0, _, _, _, _ => fun k hk => by simp at hk
  | n + 1, loc, roots, lengths, h => by
    have hTypes : List.replicate (2 * (n + 1)) ValueType.i64 =
        [.i64, .i64] ++ List.replicate (2 * n) .i64 := by
      rw [show 2 * (n + 1) = 2 + 2 * n by omega, List.replicate_add]
      rfl
    rw [hTypes, List.ofFn_succ, List.flatten_cons]
    refine (LocalsHold.append (by rfl)).mpr ⟨?_, ?_⟩
    · intro k hk
      match k, hk with
      | 0, _ => simpa [slotIndex] using (h 0).1
      | 1, _ => simpa [slotIndex] using (h 0).2
      | k + 2, hk => simp at hk
    · have hTail := LocalsHold.ofFn_pairs_of n (loc + 2) (fun i => roots i.succ)
        (fun i => lengths i.succ) (fun i => by
          have := h i.succ
          simp only [Fin.val_succ] at this
          have e1 : loc + 2 * (i.val + 1) = loc + 2 + 2 * i.val := by omega
          rw [e1] at this
          exact this)
      simpa using hTail

#print axioms heapFieldBlocks_perm
#print axioms FieldsNormal.drop_prefix
#print axioms FieldsNormal.bytesFields
#print axioms LocalsHold.ofFn_pairs

end Verified
