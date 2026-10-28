import Verified.TreeAssembleTyped
import Verified.TreeDetach

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem slotsBlocks_get_sublist (store : Store Unit) (p : UInt64) :
    ∀ (slots : List LeanExe.Pipeline.Slot) i j (hj : j < slots.length),
      List.Sublist (slotsBlocks store p (i + j) [slots[j]]) (slotsBlocks store p i slots)
  | [], _, _, hj => by simp at hj
  | slot :: slots, i, 0, _ => by
    cases slot
    · simp only [List.getElem_cons_zero, slotsBlocks]
      exact List.nil_sublist _
    · simpa only [List.getElem_cons_zero, slotsBlocks, List.append_nil, Nat.add_zero] using
        List.sublist_append_left _ (slotsBlocks store p (i + 1) slots)
    · simpa only [List.getElem_cons_zero, slotsBlocks, Nat.add_zero] using
        List.Sublist.cons₂ _ (List.nil_sublist (slotsBlocks store p (i + 1) slots))
    · simpa only [List.getElem_cons_zero, slotsBlocks, List.append_nil, Nat.add_zero] using
        List.sublist_append_left _ (slotsBlocks store p (i + 1) slots)
  | slot :: slots, i, j + 1, hj => by
    have h := slotsBlocks_get_sublist store p slots (i + 1) j (by simpa using hj)
    cases slot
    · simpa only [slotsBlocks, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using h
    · simp only [List.getElem_cons_succ, slotsBlocks]
      rw [show i + (j + 1) = i + 1 + j by omega]
      exact h.trans (List.sublist_append_right _ _)
    · simp only [List.getElem_cons_succ, slotsBlocks]
      rw [show i + (j + 1) = i + 1 + j by omega]
      exact h.trans (List.sublist_cons_self _ _)
    · simp only [List.getElem_cons_succ, slotsBlocks]
      rw [show i + (j + 1) = i + 1 + j by omega]
      exact h.trans (List.sublist_append_right _ _)

theorem Mode.node.borrow {mode : Mode} {heap : Heap} {store : Store Unit}
    {p : UInt64} {value : Node} (h : mode.node heap store p value) :
    NodeBorrowed heap store p value := by
  cases mode
  · exact h
  · exact NodeOwned.borrowed p value h.1

theorem TreeShape.fieldStart_tagSlots (shape : TreeShape) (r : Fin shape.records) :
    shape.fieldStart = (shape.tagSlots r).length :=
  (shape.fieldStart_eq r).trans (shape.tagWords_length r)

theorem TreeShape.fieldSlot_lt (shape : TreeShape) (r : Fin shape.records) (bit : Bool)
    (i : Fin ((shape.fields r).count bit)) :
    shape.fieldStart + (fieldPosition bit (shape.fields r) i).val < shape.width r := by
  have := (fieldPosition bit (shape.fields r) i).isLt
  rw [shape.fieldStart_tagSlots r, TreeShape.width]
  omega

theorem tagSlots_blocks (store : Store Unit) (p : UInt64) (shape : TreeShape)
    (r : Fin shape.records) (i : Nat) : slotsBlocks store p i (shape.tagSlots r) = [] := by
  unfold TreeShape.tagSlots
  split <;> rfl

theorem recordSlots_blocks (store : Store Unit) (p : UInt64) (shape : TreeShape)
    (r : Fin shape.records) (words arrays buffers children) :
    slotsBlocks store p 0 (shape.recordSlots r words arrays buffers children) =
      slotsBlocks store p shape.fieldStart (treeSlots (shape.fields r) words children) ++
        slotsBlocks store p (shape.fieldStart + (shape.fields r).length)
          (heapSlots (shape.kinds r) arrays buffers) := by
  unfold TreeShape.recordSlots
  rw [slotsBlocks_append, slotsBlocks_append, tagSlots_blocks, List.nil_append, Nat.zero_add,
    ← shape.fieldStart_tagSlots r, List.length_append, ← shape.fieldStart_tagSlots r,
    shape.treeSlots_length' r, Nat.zero_add]

theorem tagSlots_regions (store : Store Unit) (p : UInt64) (shape : TreeShape)
    (r : Fin shape.records) (i : Nat) : slotsRegions store p i (shape.tagSlots r) = [] := by
  unfold TreeShape.tagSlots
  split <;> rfl

theorem slotsRegions_append (store : Store Unit) (p : UInt64) (first : List LeanExe.Pipeline.Slot) :
    ∀ second i, slotsRegions store p i (first ++ second) =
      slotsRegions store p i first ++ slotsRegions store p (i + first.length) second := by
  induction first with
  | nil => intros; simp [slotsRegions]
  | cons slot rest ih =>
    intro second i
    cases slot <;> simp only [List.cons_append, slotsRegions, ih, List.length_cons,
      List.append_assoc, Nat.add_assoc, Nat.add_comm 1]

theorem recordSlots_regions (store : Store Unit) (p : UInt64) (shape : TreeShape)
    (r : Fin shape.records) (words arrays buffers children) :
    slotsRegions store p 0 (shape.recordSlots r words arrays buffers children) =
      slotsRegions store p shape.fieldStart (treeSlots (shape.fields r) words children) ++
        slotsRegions store p (shape.fieldStart + (shape.fields r).length)
          (heapSlots (shape.kinds r) arrays buffers) := by
  unfold TreeShape.recordSlots
  rw [slotsRegions_append, slotsRegions_append, tagSlots_regions, List.nil_append, Nat.zero_add,
    ← shape.fieldStart_tagSlots r, List.length_append, ← shape.fieldStart_tagSlots r,
    shape.treeSlots_length' r, Nat.zero_add]

theorem treeSlots_child_owned {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {r : Fin shape.records} {p : UInt64} {start : Nat} {words : Fin (shape.words r) → UInt64}
    {children : Fin (shape.children r) → Tree shape}
    (hSlots : SlotsOwned heap store p start
      (treeSlots (shape.fields r) words (fun i => (children i).toNode)))
    (hApart : (slotsBlocks store p start
      (treeSlots (shape.fields r) words (fun i => (children i).toNode))).Pairwise
        regionsDisjoint)
    (i : Fin (shape.children r)) :
    Mode.owned.node heap store
      (store.mem.read64 (slotAddress p (start + (fieldPosition true (shape.fields r) i).val)))
      (children i).toNode := by
  unfold TreeShape.words TreeShape.children at *
  have hi := SlotsOwned.get _ start hSlots (fieldPosition true (shape.fields r) i).val
    (by rw [treeSlots_length]; exact (fieldPosition true (shape.fields r) i).isLt)
  rw [treeSlots_child_get] at hi
  refine ⟨hi.1, ?_⟩
  have hs := slotsBlocks_get_sublist store p
    (treeSlots (shape.fields r) words (fun i => (children i).toNode)) start
    (fieldPosition true (shape.fields r) i).val
    (by rw [treeSlots_length]; exact (fieldPosition true (shape.fields r) i).isLt)
  rw [treeSlots_child_get] at hs
  simp only [slotsBlocks, List.append_nil] at hs
  exact hApart.sublist hs

theorem treeNode_word_read {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {r : Fin shape.records} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    (h : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (i : Fin (shape.words r)) :
    store.mem.read64
        (slotAddress p (shape.fieldStart + (fieldPosition false (shape.fields r) i).val)) =
      shape.slotWords r words i := by
  have hSlots : SlotsBorrowed heap store p 0 (shape.tagSlots r ++
      treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode) ++
      heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) :=
    h.borrow.2
  obtain ⟨hPrefix, -⟩ := (SlotsBorrowed.append_iff _ _ _).mp hSlots
  obtain ⟨-, hFields⟩ := (SlotsBorrowed.append_iff _ _ _).mp hPrefix
  rw [Nat.zero_add, ← shape.fieldStart_tagSlots r] at hFields
  have hLength := treeSlots_length (shape.fields r) (shape.slotWords r words)
    (fun i => (children i).toNode)
  have hi := SlotsBorrowed.get _ _ hFields (fieldPosition false (shape.fields r) i).val
    (by rw [hLength]; exact (fieldPosition false (shape.fields r) i).isLt)
  rw [treeSlots_word_get (shape.fields r) (shape.slotWords r words)
    (fun i => (children i).toNode) i] at hi
  exact hi.1

theorem treeNode_child_rep {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {r : Fin shape.records} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    (h : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (i : Fin (shape.children r)) :
    mode.node heap store
      (store.mem.read64
        (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))
      (children i).toNode := by
  cases mode
  · have hSlots : SlotsBorrowed heap store p 0 (shape.tagSlots r ++
        treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) := h.2
    obtain ⟨hPrefix, -⟩ := (SlotsBorrowed.append_iff _ _ _).mp hSlots
    obtain ⟨-, hFields⟩ := (SlotsBorrowed.append_iff _ _ _).mp hPrefix
    rw [Nat.zero_add, ← shape.fieldStart_tagSlots r] at hFields
    have hLength := treeSlots_length (shape.fields r) (shape.slotWords r words)
      (fun i => (children i).toNode)
    have hi := SlotsBorrowed.get _ _ hFields (fieldPosition true (shape.fields r) i).val
      (by rw [hLength]; exact (fieldPosition true (shape.fields r) i).isLt)
    rw [treeSlots_child_get (shape.fields r) (shape.slotWords r words)
      (fun i => (children i).toNode) i] at hi
    exact hi.1
  · have hSlots : SlotsOwned heap store p 0 (shape.tagSlots r ++
        treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) :=
      h.1.2
    obtain ⟨hPrefix, -⟩ := (SlotsOwned.append_iff _ _ _).mp hSlots
    obtain ⟨-, hFields⟩ := (SlotsOwned.append_iff _ _ _).mp hPrefix
    rw [Nat.zero_add, ← shape.fieldStart_tagSlots r] at hFields
    have hApart := (List.pairwise_cons.mp h.2).2
    change (slotsBlocks store p 0 (shape.recordSlots r (shape.slotWords r words)
      (shape.arrayWords r arrays) buffers (fun i => (children i).toNode))).Pairwise
        regionsDisjoint at hApart
    rw [recordSlots_blocks] at hApart
    exact treeSlots_child_owned hFields (List.pairwise_append.mp hApart).1 i

theorem TreeShape.heapArraySlot_lt_width (shape : TreeShape) (r : Fin shape.records)
    (i : Fin (shape.arrays r)) :
    shape.fieldStart + (shape.fields r).length + heapArraySlot (shape.kinds r) i <
      shape.width r := by
  have hLt := heapArraySlot_lt (shape.kinds r) (fun _ => #[]) (fun _ => .empty) i
  rw [heapSlots_length] at hLt
  rw [shape.fieldStart_tagSlots r]
  unfold TreeShape.width TreeShape.heapWidth
  omega

/-- The array of array field `i` of a record whose slots are owned. -/
theorem recordSlots_array_owned {heap : Heap} {store : Store Unit} {shape : TreeShape}
    {r : Fin shape.records} {p : UInt64} {words : Fin (shape.words r) → UInt64}
    {arrays : Fin (shape.arrays r) → Array UInt64}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes} {children : Fin (shape.children r) → Node}
    (hSlots : SlotsOwned heap store p 0 (shape.recordSlots r words arrays buffers children))
    (i : Fin (shape.arrays r)) :
    heap.Owned store (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
      heapArraySlot (shape.kinds r) i))) (arrays i) := by
  have hLt := heapArraySlot_lt (shape.kinds r) arrays buffers i
  have hGet := heapArraySlot_get (shape.kinds r) arrays buffers i hLt
  have hPrefixLength : (shape.tagSlots r ++ treeSlots (shape.fields r) words children).length =
      shape.fieldStart + (shape.fields r).length := by
    rw [List.length_append, ← shape.fieldStart_tagSlots r]
    exact congrArg (shape.fieldStart + ·) (treeSlots_length _ _ _)
  have hAll : SlotsOwned heap store p 0 (shape.tagSlots r ++ treeSlots (shape.fields r) words
      children ++ heapSlots (shape.kinds r) arrays buffers) := hSlots
  obtain ⟨-, hHeap⟩ := (SlotsOwned.append_iff _ _ _).mp hAll
  rw [Nat.zero_add, hPrefixLength] at hHeap
  have hi := SlotsOwned.get _ _ hHeap _ hLt
  rw [hGet] at hi
  exact hi.1

/-- The array of array field `i` of a record, held in the record's mode. -/
theorem treeNode_array_rep {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {r : Fin shape.records} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    (h : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (i : Fin (shape.arrays r)) :
    mode.array heap store
      (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
        heapArraySlot (shape.kinds r) i)))
      ((shape.arrayElem r i).words (arrays i)) := by
  have hLt := heapArraySlot_lt (shape.kinds r) (shape.arrayWords r arrays) buffers i
  have hGet := heapArraySlot_get (shape.kinds r) (shape.arrayWords r arrays) buffers i hLt
  have hPrefixLength : (shape.tagSlots r ++ treeSlots (shape.fields r) (shape.slotWords r words)
      (fun i => (children i).toNode)).length = shape.fieldStart + (shape.fields r).length := by
    rw [List.length_append, ← shape.fieldStart_tagSlots r]
    exact congrArg (shape.fieldStart + ·) (treeSlots_length _ _ _)
  cases mode
  · have hSlots : SlotsBorrowed heap store p 0 (shape.tagSlots r ++
        treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) := h.2
    obtain ⟨-, hHeap⟩ := (SlotsBorrowed.append_iff _ _ _).mp hSlots
    rw [Nat.zero_add, hPrefixLength] at hHeap
    have hi := SlotsBorrowed.get _ _ hHeap _ hLt
    rw [hGet] at hi
    exact hi.1
  · exact recordSlots_array_owned h.1.2 i

/-- A buffer field of a matched record: its root slot holds 0 exactly when it is empty, a
nonempty buffer otherwise, and the slot after it holds its length. -/
theorem treeNode_recordBuffer {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {r : Fin shape.records} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    (h : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (i : Fin (shape.buffers r)) :
    RecordBuffer heap store
      (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
        heapBufferSlot (shape.kinds r) i)))
      (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
        heapBufferSlot (shape.kinds r) i + 1)))
      (buffers i) := by
  have hLt := heapBufferSlot_lt (shape.kinds r) (shape.arrayWords r arrays) buffers i
  obtain ⟨hGet, hGetLength⟩ :=
    heapBufferSlot_get (shape.kinds r) (shape.arrayWords r arrays) buffers i hLt
  have hPrefixLength : (shape.tagSlots r ++ treeSlots (shape.fields r) (shape.slotWords r words)
      (fun i => (children i).toNode)).length = shape.fieldStart + (shape.fields r).length := by
    rw [List.length_append, ← shape.fieldStart_tagSlots r]
    exact congrArg (shape.fieldStart + ·) (treeSlots_length _ _ _)
  cases mode
  · have hSlots : SlotsBorrowed heap store p 0 (shape.tagSlots r ++
        treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) := h.2
    obtain ⟨-, hHeap⟩ := (SlotsBorrowed.append_iff _ _ _).mp hSlots
    rw [Nat.zero_add, hPrefixLength] at hHeap
    have hRoot := SlotsBorrowed.get _ _ hHeap (heapBufferSlot (shape.kinds r) i) (by omega)
    have hLength := SlotsBorrowed.get _ _ hHeap (heapBufferSlot (shape.kinds r) i + 1) hLt
    rw [hGet] at hRoot
    rw [hGetLength, ← Nat.add_assoc] at hLength
    exact ⟨hRoot.1, hLength.1⟩
  · have hSlots : SlotsOwned heap store p 0 (shape.tagSlots r ++
        treeSlots (shape.fields r) (shape.slotWords r words) (fun i => (children i).toNode) ++
        heapSlots (shape.kinds r) (shape.arrayWords r arrays) buffers) := h.1.2
    obtain ⟨-, hHeap⟩ := (SlotsOwned.append_iff _ _ _).mp hSlots
    rw [Nat.zero_add, hPrefixLength] at hHeap
    have hRoot := SlotsOwned.get _ _ hHeap (heapBufferSlot (shape.kinds r) i) (by omega)
    have hLength := SlotsOwned.get _ _ hHeap (heapBufferSlot (shape.kinds r) i + 1) hLt
    rw [hGet] at hRoot
    rw [hGetLength, ← Nat.add_assoc] at hLength
    exact ⟨hRoot.1, hLength.1⟩

/-- A buffer that a record holds is a buffer value at its root and length. -/
theorem RecordBuffer.rep {heap : Heap} {store : Store Unit} {root length : UInt64}
    {data : LeanExe.Bytes} (h : RecordBuffer heap store root length data) :
    Bytes.Rep heap store root length data := by
  obtain ⟨hBuffer, hLength⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hLength]
    apply UInt64.toNat_ofNat_of_lt'
    rcases hBuffer with ⟨-, hEmpty⟩ | ⟨-, hBuffer⟩
    · simp [UInt64.size, hEmpty]
    · have := hBuffer.capacity
      have := hBuffer.object.address
      simp only [UInt64.size]
      omega
  · rcases hBuffer with ⟨hZero, hEmpty⟩ | ⟨-, hBuffer⟩
    · exact .inl ⟨hZero, hEmpty⟩
    · exact .inr hBuffer

/-- A buffer field of a matched record: its root slot and the length slot after it hold the
buffer. -/
theorem treeNode_bytes_rep {mode : Mode} {heap : Heap} {store : Store Unit}
    {shape : TreeShape} {r : Fin shape.records} {p : UInt64}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape}
    (h : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (i : Fin (shape.buffers r)) :
    Bytes.Rep heap store
      (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
        heapBufferSlot (shape.kinds r) i)))
      (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
        heapBufferSlot (shape.kinds r) i + 1)))
      (buffers i) :=
  (treeNode_recordBuffer h i).rep

end Verified
