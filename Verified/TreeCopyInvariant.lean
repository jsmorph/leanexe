import Verified.TreeCopySources
import Verified.TreeCopyPath
import Verified.AllocCost

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

structure CopyProgress (shape : TreeShape) (heap0 : Heap) (initial : Store Unit)
    (root : List LeanExe.Pipeline.Slot) (result : UInt64) (limit : Nat)
    (heap : Heap) (store : Store Unit) (current : CopyRecord) (parents : List CopyRecord) : Prop where
  path : CopyPath root result current parents
  sources : CopySources shape heap0 initial current parents
  step : Step heap0 initial (fun _ => True) heap store (copyBlocks store current parents)
  apart : (copyBlocks store current parents).Pairwise regionsDisjoint
  budget : heap.top.toNat + allocCost (8 * shape.fields.length) *
    (current.work parents).allocations ≤ limit

structure CopyInv (shape : TreeShape) (heap0 : Heap) (initial : Store Unit)
    (root : List LeanExe.Pipeline.Slot) (result : UInt64) (limit : Nat)
    (heap : Heap) (store : Store Unit) (current : CopyRecord) (parents : List CopyRecord) : Prop
    extends CopyProgress shape heap0 initial root result limit heap store current parents where
  frames : CopyFrames shape heap store current parents

theorem CopyInv.sourceApart {shape : TreeShape} {heap0 heap : Heap} {initial store : Store Unit}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit : Nat}
    {current : CopyRecord} {parents : List CopyRecord}
    (h : CopyInv shape heap0 initial root result limit heap store current parents) :
    ∀ r ∈ (Node.record current.slots).slotRegions store current.source,
      regionsDisjoint r (block store current.pointer) := by
  intro r hr
  exact h.sources.apart h.step List.mem_cons_self r hr _
    (by simp [copyBlocks, CopyRecord.blocks])

theorem CopyInv.prefixApart {shape : TreeShape} {heap0 heap : Heap} {initial store : Store Unit}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit : Nat}
    {current : CopyRecord} {parents : List CopyRecord}
    (h : CopyInv shape heap0 initial root result limit heap store current parents) :
    ∀ b ∈ slotsBlocks store current.pointer 0 (current.slots.take current.next),
      regionsDisjoint b (block store current.pointer) := by
  have hApart := (List.pairwise_cons.mp h.apart).1
  intro b hb
  exact regionsDisjoint_symm (hApart b (List.mem_append_left _ hb))

end Verified
