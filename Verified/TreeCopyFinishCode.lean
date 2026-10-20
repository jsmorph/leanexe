import Verified.TreeCopyCompleteCode
import Verified.TreeCopyAscendCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem wp_treeCopyFinish {m : Module} {host : HostEnv Unit} {heap0 heap : Heap}
    {initial store : Store Unit} {shape : TreeShape} {root : List LeanExe.Pipeline.Slot}
    {result : UInt64} {limit base : Nat} {current : CopyRecord} {parents : List CopyRecord}
    {s0 s : Locals} {rest : Program} {Q : Assertion Unit}
    (h : CopyInv shape heap0 initial root result limit heap store current parents)
    (hLocals : CopyLocals base s0 result current.pointer s)
    (hDone : current.next = current.slots.length)
    (hLow : s.params.length ≤ base) (hHigh : base + 6 ≤ s.positions)
    (hNext : ∀ store' s' next parents',
      CopyInv shape heap0 initial root result limit heap store' next parents' →
      CopyLocals base s0 result next.pointer s' →
      CopyWork.Step (current.work parents) (next.work parents') → wp m rest Q store' s' host)
    (hRoot : ∀ store' s', NodeOwned heap store' result (.record root) →
      (Node.blocks store' result (.record root)).Pairwise regionsDisjoint →
      Step heap0 initial (fun _ => True) heap store' (Node.blocks store' result (.record root)) →
      heap.top.toNat ≤ limit → CopyLocals base s0 result current.pointer s' → Q (.Break 2 store' s')) :
    wp m (treeCopyFinish shape base ++ rest) Q store s host := by
  simp only [treeCopyFinish, List.append_assoc]
  refine wp_treeCopyComplete h hLocals hDone hLow hHigh ?_
  intro store' s' hCompleted hVars hParent
  cases parents with
  | nil =>
    change s'.get (base + 5) = some (.i64 0) at hParent
    simp only [Locals.get] at hParent
    obtain ⟨hOwned, hApart, hStep, hBudget⟩ := hCompleted.root
    simpa [wp_simp, hParent] using hRoot store' s' hOwned hApart hStep hBudget hVars
  | cons parent parents =>
    change s'.get (base + 5) = some (.i64 parent.pointer) at hParent
    have hParentFrames : CopyFrames shape heap store' parent parents := hCompleted.parents
    have hParentBase := hParentFrames.current.storage.base
    have hNonzero : parent.pointer ≠ 0 := by
      intro hZero
      rw [hZero] at hParentBase
      simp at hParentBase
    have hLow' : s'.params.length ≤ base := by
      rw [hVars.frame.params, ← hLocals.frame.params]
      exact hLow
    have hHigh' : base + 6 ≤ s'.positions := by
      rw [hVars.frame.positions, ← hLocals.frame.positions]
      exact hHigh
    have hAdvance := wp_treeCopyAscendInv (rest := rest) hCompleted hVars hParent hLow' hHigh'
      (fun store'' s'' hInv hLocals' =>
        hNext store'' s'' _ parents hInv hLocals'
          (CopyRecord.work_ascend (parent := parent) (parents := parents) hDone))
    simpa only [List.append_assoc, List.cons_append, List.nil_append, wp_localGet_cons, Locals.get_values,
      hParent, wp_eqzI64_cons, hNonzero, ite_false, wp_br_if_cons,
      ne_eq, not_true_eq_false] using hAdvance

#print axioms wp_treeCopyFinish

end Verified
