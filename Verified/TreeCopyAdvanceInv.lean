import Verified.TreeCopyInvariant
import Verified.TreeAdvance

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem CopyInv.advanceStep {shape : TreeShape} {heap0 heap : Heap}
    {initial store store' : Store Unit} {root : List LeanExe.Pipeline.Slot} {result : UInt64}
    {limit : Nat} {current : CopyRecord} {parents : List CopyRecord}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hCurrent : CopyRecord.Holds shape heap store'
      ((parents.head?.map CopyRecord.pointer).getD 0) { current with next := current.next + 1 })
    (hWrite : Step heap store (fun r => regionsDisjoint r (block store current.pointer))
      heap store' [])
    (hBlocks : ({ current with next := current.next + 1 } : CopyRecord).blocks store' =
      current.blocks store)
    (hWork : CopyWork.Step (current.work parents)
      ({ current with next := current.next + 1 }.work parents))
    (hAllocates : (current.work parents).allocates = 0) :
    CopyInv shape heap0 initial root result limit heap store'
      { current with next := current.next + 1 } parents := by
  have hKeep := h.sources.parentsKept h.step h.apart
  have hFrames := h.frames.replaceCurrent hWrite hKeep hCurrent
  have hParentBlocks : parents.flatMap (fun record => record.blocks store') =
      parents.flatMap (fun record => record.blocks store) := by
    cases parents with
    | nil => rfl
    | cons parent parents =>
      have hTail := (h.frames.2.stepKeeping hWrite hKeep).2.1
      simpa only [copyBlocks, List.flatMap_cons, List.append_eq] using hTail
  have hCopyBlocks : copyBlocks store' { current with next := current.next + 1 } parents =
      copyBlocks store current parents := by
    simp only [copyBlocks, hBlocks, hParentBlocks]
  have hAll := h.step.writeFresh hWrite (by simp [copyBlocks, CopyRecord.blocks])
  refine {
    frames := hFrames
    path := h.path.advance _
    sources := h.sources.advance _
    step := ?_
    apart := ?_
    budget := ?_
  }
  · simpa only [hCopyBlocks] using hAll
  · rw [hCopyBlocks]
    exact h.apart
  · exact hWork.allocation_bound (by rw [hAllocates]; simp) h.budget

#print axioms CopyInv.advanceStep

end Verified
