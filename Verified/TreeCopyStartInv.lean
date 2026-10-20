import Verified.TreeCopyInvariant
import Verified.RuntimeFacts

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem CopyInv.start {shape : TreeShape} {heap0 heap : Heap} {initial store : Store Unit}
    {root : List LeanExe.Pipeline.Slot} {source result : UInt64} {limit : Nat}
    (hSource : NodeBorrowed heap0 initial source (.record root))
    (hStep : Step heap0 initial (fun _ => True) heap store [block store result])
    (hRecord : CopyRecord.Holds shape heap store 0 ⟨source, result, root, 0⟩)
    (hTop : heap.top.toNat ≤ heap0.top.toNat + allocCost (8 * shape.fields.length))
    (hLimit : heap0.top.toNat + allocCost (8 * shape.fields.length) *
      (Node.record root).records ≤ limit) :
    CopyInv shape heap0 initial root result limit heap store ⟨source, result, root, 0⟩ [] := by
  have hBlocks : copyBlocks store ⟨source, result, root, 0⟩ [] = [block store result] := by
    simp only [copyBlocks, CopyRecord.blocks, List.take_zero, slotsBlocks,
      List.flatMap_nil, List.append_nil]
  refine {
    frames := hRecord
    path := .root rfl rfl
    sources := ?_
    step := ?_
    apart := ?_
    budget := ?_
  }
  · intro record hr
    simp only [List.mem_singleton] at hr
    subst record
    exact ⟨hRecord.layout, hSource⟩
  · simpa only [hBlocks] using hStep
  · rw [hBlocks]
    exact List.pairwise_singleton ..
  · simp only [CopyRecord.work, List.drop_zero, CopyWork.allocations,
      List.map_nil, List.sum_nil, Nat.add_zero]
    simp only [Node.records, Nat.mul_add, Nat.mul_one] at hLimit
    omega

theorem CopyProgress.trap {shape : TreeShape} {heap0 heap : Heap} {initial store : Store Unit}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {m : Module} {Q : Assertion Unit}
    (h : CopyProgress shape heap0 initial root result limit heap store current parents)
    (hRemaining : 0 < (current.work parents).allocations)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q) :
    TrapOK (!decide (heap.Within store m (allocCost (8 * shape.fields.length)))) Q := by
  by_cases hTotal : limit ≤ 65536 * initial.memoryCap m 0
  · have hCharge : allocCost (8 * shape.fields.length) ≤
        allocCost (8 * shape.fields.length) * (current.work parents).allocations :=
      Nat.le_mul_of_pos_right _ hRemaining
    have hWithin : heap.Within store m (allocCost (8 * shape.fields.length)) := by
      rw [Heap.Within, h.step.cap m]
      have := h.budget
      omega
    simp only [hWithin, decide_true, Bool.not_true, TrapOK]
  · by_cases hWithin : heap.Within store m (allocCost (8 * shape.fields.length))
    · simp only [hWithin, decide_true, Bool.not_true, TrapOK]
    · simpa only [hTotal, hWithin, decide_false, Bool.not_false, TrapOK] using hTrap

#print axioms CopyInv.start
#print axioms CopyProgress.trap

end Verified
