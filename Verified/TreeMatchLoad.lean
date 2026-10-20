import Verified.TreeMatchMemory
import Verified.TreeFieldPositions
import Verified.TreeFieldsLoad

namespace Verified

open Wasm LeanExe.Pipeline

theorem wp_loadTree {m : Module} {host : HostEnv Unit} {heap : Heap}
    {store : Store Unit} {s : Locals} {shape : TreeShape} {mode : Mode}
    {p : UInt64} {ptr fieldBase : Nat} {words : Fin shape.words → UInt64}
    {children : Fin shape.children → Tree shape} {rest : Program} {Q : Assertion Unit}
    (hAt : heap.At store) (hPtr : s.get ptr = some (.i64 p))
    (hNode : mode.node heap store p (Tree.node words children).toNode)
    (hLow : s.params.length ≤ fieldBase) (hPtrLow : ptr < fieldBase)
    (hRoom : fieldBase + shape.fields.length ≤ s.positions)
    (hNext : ∀ s', Frame fieldBase s s' → s'.values = s.values →
      s'.get ptr = some (.i64 p) →
      (∀ i, s'.get (fieldBase + i.val) = some (.i64 (words i))) →
      (∀ i, s'.get (fieldBase + shape.words + i.val) = some (.i64
        (store.mem.read64 (slotAddress p (fieldPosition true shape.fields i).val)))) →
      wp m rest Q store s' host) :
    wp m (treeLoadFields ptr fieldBase (fieldBase + shape.words) 0 shape.fields ++ rest)
      Q store s host := by
  dsimp only [TreeShape.words, TreeShape.children] at *
  let dsts := treeFieldLocs shape.fields fieldBase (fieldBase + shape.words)
  have hCount := shape.words_children
  have hRange : ∀ dst ∈ dsts, fieldBase ≤ dst ∧ dst < s.positions := by
    intro dst hd
    rw [treeFieldLocs_mem] at hd
    change (fieldBase ≤ dst ∧ dst < fieldBase + shape.words) ∨
      (fieldBase + shape.words ≤ dst ∧ dst < fieldBase + shape.words + shape.children) at hd
    omega
  have hDsts : ∀ dst ∈ dsts, s.params.length ≤ dst ∧ dst < s.positions ∧ dst ≠ ptr := by
    intro dst hd
    have := hRange dst hd
    omega
  have hUnique : dsts.Nodup := treeFieldLocs_nodup shape.fields _ _ (Or.inl (by rfl))
  have hFrame := recordLoadLocals_frame store p fieldBase 0 dsts s hLow
    hRange
  have hPtr' : (recordLoadLocals store p 0 dsts s).get ptr = some (.i64 p) := by
    rw [recordLoadLocals_get_other store p 0 dsts s ptr
      (fun dst hd => (hDsts dst hd).1) (by
        intro hd; exact (hDsts ptr hd).2.2 rfl)]
    exact hPtr
  have hGet := recordLoadLocals_get store p 0 dsts s hUnique
    (fun dst hd => ⟨(hDsts dst hd).1, (hDsts dst hd).2.1⟩)
  have hWords : ∀ i, (recordLoadLocals store p 0 dsts s).get (fieldBase + i.val) =
      some (.i64 (words i)) := by
    intro i
    have h := hGet (fieldPosition false shape.fields i).val
      (by rw [treeFieldLocs_length]; exact (fieldPosition false shape.fields i).isLt)
    dsimp only [dsts] at h
    rw [treeFieldLocs_word_get shape.fields fieldBase (fieldBase + shape.words) i,
      Nat.zero_add, treeNode_word_read hNode i] at h
    exact h
  have hChildren : ∀ i, (recordLoadLocals store p 0 dsts s).get
      (fieldBase + shape.words + i.val) = some (.i64
        (store.mem.read64 (slotAddress p (fieldPosition true shape.fields i).val))) := by
    intro i
    have h := hGet (fieldPosition true shape.fields i).val
      (by rw [treeFieldLocs_length]; exact (fieldPosition true shape.fields i).isLt)
    dsimp only [dsts] at h
    rw [treeFieldLocs_child_get shape.fields fieldBase (fieldBase + shape.words) i,
      Nat.zero_add] at h
    exact h
  have hSlots := hNode.borrow.1
  change RecordSlots heap p (treeSlots shape.fields words (fun i => (children i).toNode)) at hSlots
  have hLength := treeSlots_length shape.fields words (fun i => (children i).toNode)
  have hAddress : p.toNat + 8 * (0 + dsts.length) < 4294967296 := by
    simpa only [dsts, treeFieldLocs_length, Nat.zero_add, hLength] using hSlots.address
  have hMemory : p.toNat + 8 * (0 + dsts.length) ≤ store.mem.pages * 65536 := by
    have hBelow := hSlots.below
    rw [hLength] at hBelow
    rw [Nat.zero_add, treeFieldLocs_length]
    exact hBelow.trans hAt.top
  rw [treeLoadFields_eq]
  exact wp_recordLoadCode 0 dsts s hPtr hDsts hAddress hMemory
    (hNext _ hFrame (recordLoadLocals_values store p 0 dsts s) hPtr' hWords hChildren)

end Verified
