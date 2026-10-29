import Verified.TreeCopyInvariant
import Verified.RuntimeFacts

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem CopyProgress.trap {shape : TreeShape} {heap0 heap : Heap} {initial store : Store Unit}
    {root : List LeanExe.Pipeline.Slot} {result : UInt64} {limit : Nat}
    {current : CopyRecord} {parents : List CopyRecord} {m : Module} {Q : Assertion Unit}
    (h : CopyProgress shape heap0 initial root result limit heap store current parents)
    {width : Nat} (hCharge : allocCost (8 * width) ≤ (current.work parents).cost)
    (hTrap : TrapOK (!decide (limit ≤ 65536 * initial.memoryCap m 0)) Q) :
    TrapOK (!decide (heap.Within store m (allocCost (8 * width)))) Q := by
  by_cases hTotal : limit ≤ 65536 * initial.memoryCap m 0
  · have hWithin : heap.Within store m (allocCost (8 * width)) := by
      rw [Heap.Within, h.step.cap m]
      have := h.budget
      omega
    simp only [hWithin, decide_true, Bool.not_true, TrapOK]
  · by_cases hWithin : heap.Within store m (allocCost (8 * width))
    · simp only [hWithin, decide_true, Bool.not_true, TrapOK]
    · simpa only [hTotal, hWithin, decide_false, Bool.not_false, TrapOK] using hTrap

#print axioms CopyProgress.trap

end Verified
