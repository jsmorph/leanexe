import Verified.TreeMatchMemory
import Verified.TreeFieldPositions
import Verified.TreeFieldsLoad

namespace Verified

open Wasm LeanExe.Pipeline

theorem wp_loadTree {m : Module} {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {r : Fin shape.records} {mode : Mode}
    {p : UInt64} {ptr fieldBase : Nat} {words : Fin (shape.words r) → UInt64}
    {children : Fin (shape.children r) → Tree shape} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hNode : mode.node heap store p (Tree.node r words children).toNode)
    (hLow : s.params.length ≤ fieldBase) (hPtrLow : ptr < fieldBase)
    (hRoom : fieldBase + (shape.fields r).length ≤ s.positions)
    (hNext : ∀ s', Frame fieldBase s s' → s'.values = s.values →
      s'.get ptr = some (.i64 p) →
      (∀ i, s'.get (fieldBase + i.val) = some (.i64 (words i))) →
      (∀ i, s'.get (fieldBase + shape.words r + i.val) = some (.i64
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val))))) →
      wp m rest Q store s' host) :
    wp m (treeLoadFields ptr fieldBase (fieldBase + shape.words r) shape.fieldStart
      (shape.fields r) ++ rest) Q store s host := by
  have hStart := shape.fieldStart_tagSlots r
  dsimp only [TreeShape.words, TreeShape.children] at *
  let dsts := treeFieldLocs (shape.fields r) fieldBase (fieldBase + shape.words r)
  have hCount := shape.words_children r
  have hRange : ∀ dst ∈ dsts, fieldBase ≤ dst ∧ dst < s.positions := by
    intro dst hd
    rw [treeFieldLocs_mem] at hd
    change (fieldBase ≤ dst ∧ dst < fieldBase + shape.words r) ∨
      (fieldBase + shape.words r ≤ dst ∧
        dst < fieldBase + shape.words r + shape.children r) at hd
    omega
  have hDsts : ∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions ∧ dst ≠ ptr := by
    intro dst hd
    have := hRange dst hd
    omega
  have hUnique : dsts.Nodup := treeFieldLocs_nodup (shape.fields r) _ _ (Or.inl (by rfl))
  have hFrame := recordLoadLocals_frame store p fieldBase shape.fieldStart dsts s hLow
    hRange
  have hPtr' : (recordLoadLocals store p shape.fieldStart dsts s).get ptr = some (.i64 p) := by
    rw [recordLoadLocals_get_other store p shape.fieldStart dsts s ptr
      (fun dst hd => (hDsts dst hd).1) (by
        intro hd; exact (hDsts ptr hd).2.2 rfl)]
    exact hPtr
  have hGet := recordLoadLocals_get store p shape.fieldStart dsts s hUnique
    (fun dst hd => ⟨(hDsts dst hd).1, (hDsts dst hd).2.1⟩)
  have hWords : ∀ i, (recordLoadLocals store p shape.fieldStart dsts s).get (fieldBase + i.val) =
      some (.i64 (words i)) := by
    intro i
    have h := hGet (fieldPosition false (shape.fields r) i).val
      (by rw [treeFieldLocs_length]; exact (fieldPosition false (shape.fields r) i).isLt)
    dsimp only [dsts] at h
    rw [treeFieldLocs_word_get (shape.fields r) fieldBase (fieldBase + shape.words r) i,
      treeNode_word_read hNode i] at h
    exact h
  have hChildren : ∀ i, (recordLoadLocals store p shape.fieldStart dsts s).get
      (fieldBase + shape.words r + i.val) = some (.i64
        (store.mem.read64
          (slotAddress p (shape.fieldStart + (fieldPosition true (shape.fields r) i).val)))) := by
    intro i
    have h := hGet (fieldPosition true (shape.fields r) i).val
      (by rw [treeFieldLocs_length]; exact (fieldPosition true (shape.fields r) i).isLt)
    dsimp only [dsts] at h
    rw [treeFieldLocs_child_get (shape.fields r) fieldBase (fieldBase + shape.words r) i] at h
    exact h
  have hSlots := hNode.borrow.1
  change RecordSlots heap p (shape.recordSlots r words (fun i => (children i).toNode)) at hSlots
  have hLength := shape.recordSlots_length r words (fun i => (children i).toNode)
  have hWidth : shape.width r = shape.fieldStart + (shape.fields r).length := by
    rw [hStart]
    rfl
  have hAddress : p.toNat + 8 * (shape.fieldStart + dsts.length) < 4294967296 := by
    have := hSlots.address
    rw [hLength, hWidth] at this
    simpa only [dsts, treeFieldLocs_length] using this
  have hMemory : p.toNat + 8 * (shape.fieldStart + dsts.length) ≤ store.mem.pages * 65536 := by
    have hBelow := hSlots.below
    rw [hLength, hWidth] at hBelow
    rw [treeFieldLocs_length]
    exact hBelow.trans hAt.top
  rw [treeLoadFields_eq]
  exact wp_recordLoadCode shape.fieldStart dsts s hPtr hDsts hAddress hMemory
    (hNext _ hFrame (recordLoadLocals_values store p shape.fieldStart dsts s) hPtr' hWords
      hChildren)

end Verified
