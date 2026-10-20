import Verified.TreeCopyCompleteInv

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem CopyCompleted.ascend {shape : TreeShape} {heap0 heap : Heap}
    {initial store store' : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current parent : CopyRecord} {parents : List CopyRecord}
    (h : CopyCompleted shape heap0 initial root result limit heap store current (parent :: parents))
    (hParent : CopyRecord.Holds shape heap store'
      ((parents.head?.map CopyRecord.pointer).getD 0) { parent with next := parent.next + 1 })
    (hWrite : Step heap store (fun r => regionsDisjoint r (block store parent.pointer)) heap store' [])
    (hParentBlocks : ({ parent with next := parent.next + 1 } : CopyRecord).blocks store' =
      parent.blocks store ++ Node.blocks store current.pointer (.record current.slots)) :
    CopyInv shape heap0 initial root result limit heap store'
      { parent with next := parent.next + 1 } parents := by
  have hSources : CopySources shape heap0 initial parent parents :=
    fun record hr => h.sources record (List.mem_cons_of_mem current hr)
  have hStepTail : Step heap0 initial (fun _ => True) heap store (copyBlocks store parent parents) :=
    h.step.mono (fun _ _ => trivial) (fun _ hb => List.mem_append_right _ hb)
  have hApartTail : (copyBlocks store parent parents).Pairwise regionsDisjoint :=
    (List.pairwise_append.mp h.apart).2.1
  have hKeep := hSources.parentsKept hStepTail hApartTail
  have hFrames := h.parents.replaceCurrent hWrite hKeep hParent
  have hAncestors : parents.flatMap (fun record => record.blocks store') =
      parents.flatMap (fun record => record.blocks store) := by
    cases parents with
    | nil => rfl
    | cons ancestor parents =>
      have hTail := (h.parents.2.stepKeeping hWrite hKeep).2.1
      simpa only [copyBlocks, List.flatMap_cons, List.append_eq] using hTail
  have hNewBlocks : copyBlocks store' { parent with next := parent.next + 1 } parents =
      (parent.blocks store ++ current.blocks store) ++
        parents.flatMap (fun record => record.blocks store) := by
    simp only [copyBlocks, hParentBlocks, hAncestors, current.blocks_done store h.done]
  have hOldBlocks : copyBlocks store current (parent :: parents) =
      (current.blocks store ++ parent.blocks store) ++
        parents.flatMap (fun record => record.blocks store) := by
    simp only [copyBlocks, List.flatMap_cons, List.append_assoc]
  have hPerm : (copyBlocks store current (parent :: parents)).Perm
      (copyBlocks store' { parent with next := parent.next + 1 } parents) := by
    rw [hOldBlocks, hNewBlocks]
    exact List.perm_append_comm.append_right _
  have hAll := h.step.writeFresh hWrite (by simp [copyBlocks, CopyRecord.blocks])
  refine {
    frames := hFrames
    path := ?_
    sources := hSources.advance _
    step := hAll.mono (fun _ _ => trivial) (fun _ hb => hPerm.mem_iff.mpr hb)
    apart := h.apart.perm hPerm (fun h => regionsDisjoint_symm h)
    budget := ?_
  }
  · cases h.path with
    | child _ _ rest => exact rest.advance _
  · have hWork := CopyRecord.work_ascend (parent := parent) (parents := parents) h.done
    have hAllocates : (current.work (parent :: parents)).allocates = 0 := by
      simp only [CopyRecord.work, h.done, List.drop_length, CopyWork.allocates]
    exact hWork.allocation_bound (by rw [hAllocates]; simp) h.budget

#print axioms CopyCompleted.ascend

end Verified
