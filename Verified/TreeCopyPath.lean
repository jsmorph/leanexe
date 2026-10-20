import Verified.TreeCopyState

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

inductive CopyPath (root : List LeanExe.Pipeline.Slot) (result : UInt64) :
    CopyRecord → List CopyRecord → Prop where
  | root {current} (slots : current.slots = root) (pointer : current.pointer = result) :
      CopyPath root result current []
  | child {current parent parents} (bound : parent.next < parent.slots.length)
      (slot : parent.slots[parent.next] = .child (.record current.slots))
      (rest : CopyPath root result parent parents) :
      CopyPath root result current (parent :: parents)

theorem CopyPath.advance {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {current : CopyRecord} {parents : List CopyRecord} (h : CopyPath root result current parents)
    (next : Nat) : CopyPath root result { current with next } parents := by
  cases h with
  | root slots pointer => exact .root slots pointer
  | child bound slot rest => exact .child bound slot rest

theorem CopyRecord.work_advance {current : CopyRecord} {parents : List CopyRecord}
    {word : UInt64} (h : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .word word) :
    CopyWork.Step (current.work parents) ({ current with next := current.next + 1 }.work parents) := by
  unfold CopyRecord.work
  rw [List.drop_eq_getElem_cons h, hSlot]
  exact .word

theorem CopyRecord.work_null {current : CopyRecord} {parents : List CopyRecord}
    (h : current.next < current.slots.length) (hSlot : current.slots[current.next] = .child .null) :
    CopyWork.Step (current.work parents) ({ current with next := current.next + 1 }.work parents) := by
  unfold CopyRecord.work
  rw [List.drop_eq_getElem_cons h, hSlot]
  exact .null

theorem CopyRecord.work_descend {current child : CopyRecord} {parents : List CopyRecord}
    (h : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .child (.record child.slots)) (hNext : child.next = 0) :
    CopyWork.Step (current.work parents) (child.work (current :: parents)) := by
  unfold CopyRecord.work
  rw [List.drop_eq_getElem_cons h, hSlot, hNext]
  simp only [List.drop_zero, List.map_cons]
  exact .descend

theorem CopyRecord.work_ascend {current parent : CopyRecord} {parents : List CopyRecord}
    (h : current.next = current.slots.length) :
    CopyWork.Step (current.work (parent :: parents))
      ({ parent with next := parent.next + 1 }.work parents) := by
  simp only [CopyRecord.work, h, List.drop_length, List.map_cons]
  exact .ascend

theorem CopyRecord.work_finish {current : CopyRecord} (h : current.next = current.slots.length) :
    CopyWork.Step (current.work []) .done := by
  simp only [CopyRecord.work, h, List.drop_length, List.map_nil]
  exact .finish

#print axioms CopyPath.advance
#print axioms CopyRecord.work_descend

end Verified
