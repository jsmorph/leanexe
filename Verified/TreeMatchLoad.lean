import Verified.TreeMatchMemory
import Verified.TreeFieldPositions
import Verified.TreeFieldsLoad
import Verified.TreeHeapFields

namespace Verified

open Wasm LeanExe.Pipeline

theorem wp_loadTree {m : Module} {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode}
    {p : UInt64} {h ptr fieldBase : Nat}
    {words : (i : Fin (shape.words r)) → (shape.elem r i).denote}
    {arrays : (i : Fin (shape.arrays r)) → Array (shape.arrayElem r i).denote}
    {buffers : Fin (shape.buffers r) → LeanExe.Bytes}
    {children : Fin (shape.children r) → Tree shape} {rest : Program} {Q : Assertion Unit}
    (hh : s.positions = h)
    (hAt : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hNode : mode.node heap store p (Tree.node r words arrays buffers children).toNode)
    (hLow : s.params.length ≤ fieldBase) (hPtrLow : ptr < fieldBase)
    (hRoom : fieldBase + shape.words r + shape.children r + shape.arrays r +
      2 * shape.buffers r ≤ s.positions)
    (hNext : ∀ s', Frame fieldBase s s' → s'.values = s.values →
      s'.get ptr = some (.i64 p) →
      (∀ i, s'.get (slotIndex s.positions (fieldBase + i.val) (shape.elem r i).slotType) =
        some (typedValue (shape.elem r i).slotType (shape.slotWords r words i))) →
      (∀ i, s'.get (fieldBase + shape.words r + i.val) = some (.i64
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val))))) →
      (∀ i, s'.get (fieldBase + shape.words r + shape.children r + i.val) = some (.i64
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapArraySlot (shape.kinds r) i))))) →
      (∀ i, s'.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val) =
          some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
            (shape.fields r).length + heapBufferSlot (shape.kinds r) i)))) ∧
        s'.get (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val + 1) =
          some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
            (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1))))) →
      wp m rest Q store s' host) :
    wp m (treeLoadFields h ptr (shape.wordTypes r) fieldBase (fieldBase + shape.words r)
      shape.fieldStart (shape.fields r) ++
      treeLoadHeaps ptr (shape.kinds r) (fieldBase + shape.words r + shape.children r)
        (fieldBase + shape.words r + shape.children r + shape.arrays r)
        (shape.fieldStart + (shape.fields r).length) ++ rest) Q store s host := by
  subst hh
  have hStart := shape.fieldStart_tagSlots r
  have hTypes : ∀ i : Fin (shape.words r),
      (shape.wordTypes r).getD i.val .i64 = (shape.elem r i).slotType := by
    intro i
    simp [TreeShape.wordTypes, i.isLt]
  have hCount := shape.words_children r
  let arraysBase := fieldBase + shape.words r + shape.children r
  let buffersBase := fieldBase + shape.words r + shape.children r + shape.arrays r
  let fieldDsts := treeFieldLocs (shape.fields r) fieldBase (fieldBase + shape.words r)
  let heapDsts := heapLocs (shape.kinds r) arraysBase buffersBase
  let dsts := fieldDsts ++ heapDsts
  let tys := treeFieldTypes (shape.fields r) (shape.wordTypes r)
  have hFieldRange : ∀ dst ∈ fieldDsts, fieldBase ≤ dst ∧ dst < arraysBase := by
    intro dst hd
    rw [treeFieldLocs_mem] at hd
    change (fieldBase ≤ dst ∧ dst < fieldBase + shape.words r) ∨
      (fieldBase + shape.words r ≤ dst ∧
        dst < fieldBase + shape.words r + shape.children r) at hd
    dsimp only [arraysBase]
    omega
  have hHeapRange : ∀ dst ∈ heapDsts, arraysBase ≤ dst ∧ dst < s.positions := by
    intro dst hd
    have := heapLocs_mem (shape.kinds r) arraysBase buffersBase dst hd
    change (arraysBase ≤ dst ∧ dst < arraysBase + shape.arrays r) ∨
      (buffersBase ≤ dst ∧ dst < buffersBase + 2 * shape.buffers r) at this
    dsimp only [arraysBase, buffersBase] at this ⊢
    omega
  have hRange : ∀ dst ∈ dsts, fieldBase ≤ dst ∧ dst < s.positions := by
    intro dst hd
    rcases List.mem_append.mp hd with hd | hd
    · have := hFieldRange dst hd
      dsimp only [arraysBase] at this
      omega
    · have := hHeapRange dst hd
      dsimp only [arraysBase] at this
      omega
  have hDsts : ∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions ∧ dst ≠ ptr := by
    intro dst hd
    have := hRange dst hd
    omega
  have hUnique : dsts.Nodup := by
    refine List.nodup_append.mpr ⟨treeFieldLocs_nodup (shape.fields r) _ _ (Or.inl (by rfl)),
      heapLocs_nodup (shape.kinds r) _ _ (Or.inl (by dsimp only [arraysBase, buffersBase]; rfl)),
      fun a ha b hb hab => ?_⟩
    have h1 := hFieldRange a ha
    have h2 := hHeapRange b hb
    omega
  have hFrame := recordLoadLocals_frame store p fieldBase shape.fieldStart dsts tys s hLow
    hRange
  have hPtr' : (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get ptr =
      some (.i64 p) := by
    rw [recordLoadLocals_get_other store p s.positions shape.fieldStart dsts tys s ptr
      (fun dst hd ty => by
        obtain ⟨hl, hh', -⟩ := hDsts dst hd
        have hb := hRange dst hd
        refine ⟨(slotIndex_bounds (s := s) ty hl hh').1, ?_⟩
        cases ty <;> simp only [slotIndex] <;> omega)]
    exact hPtr
  have hGet := recordLoadLocals_get store p shape.fieldStart dsts tys s hUnique
    (fun dst hd => ⟨(hDsts dst hd).1, (hDsts dst hd).2.1⟩)
  have hFieldLen : fieldDsts.length = (shape.fields r).length := treeFieldLocs_length _ _ _
  have hWords : ∀ i, (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
      (slotIndex s.positions (fieldBase + i.val) (shape.elem r i).slotType) =
      some (typedValue (shape.elem r i).slotType (shape.slotWords r words i)) := by
    intro i
    have hPos := (fieldPosition false (shape.fields r) i).isLt
    have hj := hGet (fieldPosition false (shape.fields r) i).val
      (by rw [List.length_append, hFieldLen]; omega)
    rw [List.getElem_append_left (by rw [hFieldLen]; exact hPos)] at hj
    dsimp only [fieldDsts, tys] at hj
    rw [treeFieldLocs_word_get (shape.fields r) fieldBase (fieldBase + shape.words r) i,
      treeFieldTypes_word_get (shape.fields r) (shape.wordTypes r) i, hTypes i,
      treeNode_word_read hNode i] at hj
    exact hj
  have hChildren : ∀ i, (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
      (fieldBase + shape.words r + i.val) = some (.i64
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))) := by
    intro i
    have hPos := (fieldPosition true (shape.fields r) i).isLt
    have hj := hGet (fieldPosition true (shape.fields r) i).val
      (by rw [List.length_append, hFieldLen]; omega)
    rw [List.getElem_append_left (by rw [hFieldLen]; exact hPos)] at hj
    dsimp only [fieldDsts, tys] at hj
    rw [treeFieldLocs_child_get (shape.fields r) fieldBase (fieldBase + shape.words r) i,
      treeFieldTypes_child_get (shape.fields r) (shape.wordTypes r) i] at hj
    simpa only [slotIndex, typedValue] using hj
  have hArrays : ∀ i, (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
      (fieldBase + shape.words r + shape.children r + i.val) = some (.i64
        (store.mem.read64 (slotAddress p (shape.fieldStart + (shape.fields r).length +
          heapArraySlot (shape.kinds r) i)))) := by
    intro i
    have hLt := heapArraySlot_lt (shape.kinds r) (fun _ => #[]) (fun _ => .empty) i
    rw [heapSlots_length] at hLt
    have hHeapLen := heapLocs_length (shape.kinds r) arraysBase buffersBase
    have hj := hGet (fieldDsts.length + heapArraySlot (shape.kinds r) i)
      (by rw [List.length_append, hHeapLen]; omega)
    rw [List.getElem_append_right (by omega)] at hj
    simp only [Nat.add_sub_cancel_left] at hj
    rw [heapLocs_array_get (shape.kinds r) arraysBase buffersBase i (by rw [hHeapLen]; omega)]
      at hj
    have hTy : tys.getD (fieldDsts.length + heapArraySlot (shape.kinds r) i) .i64 = .i64 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        dsimp only [tys]
        rw [treeFieldTypes_length, ← hFieldLen]
        omega)]
      rfl
    rw [hTy, hFieldLen, ← Nat.add_assoc] at hj
    simpa only [slotIndex, typedValue, arraysBase] using hj
  have hBuffers : ∀ i, (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
        (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val) =
        some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i)))) ∧
      (recordLoadLocals store p s.positions shape.fieldStart dsts tys s).get
        (fieldBase + shape.words r + shape.children r + shape.arrays r + 2 * i.val + 1) =
        some (.i64 (store.mem.read64 (slotAddress p (shape.fieldStart +
          (shape.fields r).length + heapBufferSlot (shape.kinds r) i + 1)))) := by
    intro i
    have hLt := heapBufferSlot_lt (shape.kinds r) (fun _ => #[]) (fun _ => .empty) i
    rw [heapSlots_length] at hLt
    have hHeapLen := heapLocs_length (shape.kinds r) arraysBase buffersBase
    obtain ⟨hLoc1, hLoc2⟩ := heapLocs_buffer_get (shape.kinds r) arraysBase buffersBase i
      (by rw [hHeapLen]; omega)
    have hj1 := hGet (fieldDsts.length + heapBufferSlot (shape.kinds r) i)
      (by rw [List.length_append, hHeapLen]; omega)
    have hj2 := hGet (fieldDsts.length + (heapBufferSlot (shape.kinds r) i + 1))
      (by rw [List.length_append, hHeapLen]; omega)
    rw [List.getElem_append_right (by omega)] at hj1 hj2
    simp only [Nat.add_sub_cancel_left] at hj1 hj2
    rw [hLoc1] at hj1
    rw [hLoc2] at hj2
    have hTy (k : Nat) : tys.getD (fieldDsts.length + k) .i64 = .i64 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
        dsimp only [tys]
        rw [treeFieldTypes_length, ← hFieldLen]
        omega)]
      rfl
    rw [hTy, hFieldLen] at hj1 hj2
    refine ⟨?_, ?_⟩
    · simpa only [slotIndex, typedValue, buffersBase, Nat.add_assoc] using hj1
    · simpa only [slotIndex, typedValue, buffersBase, Nat.add_assoc] using hj2
  have hSlots := hNode.borrow.1
  change RecordSlots heap p (shape.recordSlots r (shape.slotWords r words)
    (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)) at hSlots
  have hLength := shape.recordSlots_length r (shape.slotWords r words)
    (shape.arrayWords r arrays) buffers (fun i => (children i).toNode)
  have hDstsLen : dsts.length = (shape.fields r).length + shape.heapWidth r := by
    dsimp only [dsts]
    rw [List.length_append, hFieldLen, heapLocs_length]
    rfl
  have hWidth : shape.width r = shape.fieldStart + dsts.length := by
    rw [hDstsLen, hStart]
    simp only [TreeShape.width]
    omega
  have hAddress : p.toNat + 8 * (shape.fieldStart + dsts.length) < 4294967296 := by
    have := hSlots.address
    rw [hLength, hWidth] at this
    exact this
  have hMemory : p.toNat + 8 * (shape.fieldStart + dsts.length) ≤ store.mem.pages * 65536 := by
    have hBelow := hSlots.below
    rw [hLength, hWidth] at hBelow
    exact hBelow.trans hAt.top
  have hPtrPos : ptr < s.positions := by omega
  rw [treeLoadFields_eq, treeLoadHeaps_eq s.positions,
    show shape.fieldStart + (shape.fields r).length = shape.fieldStart + fieldDsts.length by
      rw [hFieldLen],
    ← recordLoadCode_append _ _ _ _ _ _ [] (by
      rw [treeFieldTypes_length, treeFieldLocs_length]), List.append_nil]
  exact wp_recordLoadCode shape.fieldStart dsts tys s hPtr hPtrPos hDsts hAddress hMemory
    (hNext _ hFrame (recordLoadLocals_values store p s.positions shape.fieldStart dsts tys s)
      hPtr' hWords hChildren hArrays hBuffers)

end Verified
