import Verified.TreeCopyInvariant

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem CopyInv.descend {shape : TreeShape} {heap0 heap heap' : Heap}
    {initial store store' : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current child : CopyRecord} {parents : List CopyRecord}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hBound : current.next < current.slots.length)
    (hSlot : current.slots[current.next] = .child (.record child.slots)) (hNext : child.next = 0)
    (hChildSource : NodeBorrowed heap0 initial child.source (.record child.slots))
    (hNew : Step heap store (fun _ => True) heap' store' [block store' child.pointer])
    (hChild : child.Holds shape heap' store' current.pointer)
    (hTop : heap'.top.toNat ≤ heap.top.toNat + allocCost (8 * child.slots.length)) :
    CopyInv shape heap0 initial root result limit heap' store' child (current :: parents) := by
  obtain ⟨hFrames, hBlocks, hApart⟩ := h.frames.step hNew
  have hCopyBlocks : copyBlocks store' child (current :: parents) =
      block store' child.pointer :: copyBlocks store current parents := by
    simp only [copyBlocks, CopyRecord.blocks, hNext, List.take_zero, slotsBlocks,
      List.cons_append, List.nil_append, List.flatMap_cons] at hBlocks ⊢
    exact congrArg (List.cons (block store' child.pointer)) hBlocks
  have hAll := h.step.transBoth hNew (keep := fun _ => True)
    (fun _ _ => ⟨trivial, fun _ => trivial⟩)
  refine {
    frames := ⟨hChild, hFrames⟩
    path := .child hBound hSlot h.path
    sources := ?_
    step := ?_
    apart := ?_
    budget := ?_
  }
  · intro record hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨hChild.layout, hChildSource⟩
    · exact h.sources record hr
  · apply hAll.mono (fun _ _ => trivial)
    intro b hb
    rw [hCopyBlocks] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact List.mem_append_right _ (by simp)
    · exact List.mem_append_left _ hb
  · rw [hCopyBlocks]
    exact List.pairwise_cons.mpr ⟨fun b hb => regionsDisjoint_symm (hApart b hb _ (by simp)), h.apart⟩
  · have hWork := CopyRecord.work_descend (parents := parents) hBound hSlot hNext
    have hCharge : (current.work parents).charge = allocCost (8 * child.slots.length) := by
      unfold CopyRecord.work
      rw [List.drop_eq_getElem_cons hBound, hSlot]
      rfl
    exact hWork.cost_bound (by rw [hCharge]; exact hTop) h.budget

#print axioms CopyInv.descend

end Verified
