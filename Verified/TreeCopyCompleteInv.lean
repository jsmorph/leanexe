import Verified.TreeCopyInvariant

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def CopyParentFrames (shape : TreeShape) (heap : Heap) (store : Store Unit) :
    List CopyRecord → Prop
  | [] => True
  | parent :: parents => CopyFrames shape heap store parent parents

structure CopyCompleted (shape : TreeShape) (heap0 : Heap) (initial : Store Unit)
    (root : List LeanExe.Pipeline.Slot) (result : UInt64) (limit : Nat)
    (heap : Heap) (store : Store Unit) (current : CopyRecord) (parents : List CopyRecord) : Prop
    extends CopyProgress shape heap0 initial root result limit heap store current parents where
  done : current.next = current.slots.length
  owned : NodeOwned heap store current.pointer (.record current.slots)
  parents : CopyParentFrames shape heap store parents

theorem CopyRecord.blocks_done (store : Store Unit) (current : CopyRecord)
    (h : current.next = current.slots.length) :
    current.blocks store = Node.blocks store current.pointer (.record current.slots) := by
  simp only [CopyRecord.blocks, h, List.take_length, Node.blocks]

theorem CopyInv.complete {shape : TreeShape} {heap0 heap : Heap}
    {initial store store' : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current : CopyRecord} {parents : List CopyRecord}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hDone : current.next = current.slots.length)
    (hWrites : Memory.WritesRange store store' (current.pointer.toNat - 40) current.pointer.toNat)
    (hAt : heap.At store') (hOwned : NodeOwned heap store' current.pointer (.record current.slots))
    (hNodeBlocks : Node.blocks store' current.pointer (.record current.slots) =
      Node.blocks store current.pointer (.record current.slots)) :
    CopyCompleted shape heap0 initial root result limit heap store' current parents := by
  have hCurrent := h.frames.current
  have hBase := hCurrent.storage.base
  have hWrite : Step heap store (fun r => regionsDisjoint r (block store current.pointer))
      heap store' [] :=
    Step.ofWritesRange hAt hWrites (by simp only [block]; omega) (by simp only [block]; omega)
  have hKeep := h.sources.parentsKept h.step h.apart
  have hParentFrames : CopyParentFrames shape heap store' parents := by
    cases parents with
    | nil => trivial
    | cons parent parents => exact (h.frames.2.stepKeeping hWrite hKeep).1
  have hParentBlocks : parents.flatMap (fun record => record.blocks store') =
      parents.flatMap (fun record => record.blocks store) := by
    cases parents with
    | nil => rfl
    | cons parent parents =>
      have hTail := (h.frames.2.stepKeeping hWrite hKeep).2.1
      simpa only [copyBlocks, List.flatMap_cons, List.append_eq] using hTail
  have hCurrentBlocks : current.blocks store' = current.blocks store := by
    rw [current.blocks_done store' hDone, current.blocks_done store hDone]
    exact hNodeBlocks
  have hCopyBlocks : copyBlocks store' current parents = copyBlocks store current parents := by
    simp only [copyBlocks, hCurrentBlocks, hParentBlocks]
  have hAll := h.step.writeFresh hWrite (by simp [copyBlocks, CopyRecord.blocks])
  refine {
    done := hDone
    owned := hOwned
    parents := hParentFrames
    path := h.path
    sources := h.sources
    step := ?_
    apart := ?_
    budget := h.budget
  }
  · simpa only [hCopyBlocks] using hAll
  · rw [hCopyBlocks]
    exact h.apart

theorem CopyCompleted.root {shape : TreeShape} {heap0 heap : Heap} {initial store : Store Unit}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit : Nat} {current : CopyRecord}
    (h : CopyCompleted shape heap0 initial root result limit heap store current []) :
    NodeOwned heap store result (.record root) ∧
      (Node.blocks store result (.record root)).Pairwise regionsDisjoint ∧
      Step heap0 initial (fun _ => True) heap store (Node.blocks store result (.record root)) ∧
      heap.top.toNat ≤ limit := by
  cases h.path with
  | root hSlots hPointer =>
    have hBlocks : copyBlocks store current [] = Node.blocks store result (.record root) := by
      simp only [copyBlocks, List.flatMap_nil, List.append_nil, current.blocks_done store h.done,
        hSlots, hPointer]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [hSlots, hPointer] using h.owned
    · simpa only [hBlocks] using h.apart
    · simpa only [hBlocks] using h.step
    · have := h.budget
      omega

#print axioms CopyInv.complete
#print axioms CopyCompleted.root

end Verified
