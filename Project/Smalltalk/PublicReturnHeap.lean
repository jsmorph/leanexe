import Project.Smalltalk.ReturnHeap
import Project.Smalltalk.ReturnChecks
import Project.Smalltalk.CallChainReachability
import Project.Smalltalk.InstructionHeap
import Project.Smalltalk.SelectedReturnHeap

namespace Project.Smalltalk.PublicReturnHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.Reachability

theorem accepted_target {s : Array UInt64} {target : UInt64}
    (accepted : ¬ (kind s target != 5 || field s target 3 == dead || !onChain s target) = true) :
    kind s target = 5 ∧ onChain s target = true := by
  constructor
  · apply Classical.byContradiction
    intro different
    have test := bne_iff_ne.mpr different
    have rejected : (kind s target != 5 || field s target 3 == dead || !onChain s target) = true := by
      simp only [test, Bool.true_or]
    exact accepted rejected
  · cases scan : onChain s target
    · have rejected : (kind s target != 5 || field s target 3 == dead || !onChain s target) = true := by
        simp only [scan, Bool.not_false, Bool.or_true]
      exact False.elim (accepted rejected)
    · rfl

theorem ret_valid {p s : Array UInt64} {cap : Nat}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4)
    (activation : kind s (read s 2) = 5) (nonlocal : UInt64) :
    Heap.Valid (ret p s nonlocal) cap ∧ PointerTypes.Valid (ret p s nonlocal) cap := by
  let target := ReturnChecks.selected p s nonlocal
  let stack := field s (read s 2) 7
  rw [ReturnChecks.ret_eq]
  change Heap.Valid (if kind s stack != 7 then fail s 4 else
      if kind s target != 5 || field s target 3 == dead || !onChain s target then fail s 7 else
      returnReserved s target (field s target 4) (field s stack 2)) cap ∧
    PointerTypes.Valid (if kind s stack != 7 then fail s 4 else
      if kind s target != 5 || field s target 3 == dead || !onChain s target then fail s 7 else
      returnReserved s target (field s target 4) (field s stack 2)) cap
  by_cases stackCell : kind s stack = 7
  · simp only [show (kind s stack != 7) = false by rw [stackCell]; rfl, Bool.false_eq_true, ite_false]
    by_cases rejected : (kind s target != 5 || field s target 3 == dead || !onChain s target) = true
    · simp only [rejected, ite_true]
      exact ⟨Heap.fail_valid valid 7, TypedCollection.fail_typed valid.1.1 typed 7⟩
    · simp only [rejected, Bool.false_eq_true, ite_false]
      have accepted := accepted_target rejected
      have reached := CallChainReachability.onChain_reachable valid.1 accepted.2
      exact SelectedReturnHeap.selected_valid (s := s) (cap := cap) (target := target)
        valid typed phase activation accepted.1 reached stackCell
  · simp only [show (kind s stack != 7) = true from bne_iff_ne.mpr stackCell, ite_true]
    exact ⟨Heap.fail_valid valid 4, TypedCollection.fail_typed valid.1.1 typed 4⟩

end Project.Smalltalk.PublicReturnHeap
