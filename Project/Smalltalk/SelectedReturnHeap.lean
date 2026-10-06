import Project.Smalltalk.ReturnHeap
import Project.Smalltalk.InstructionHeap

namespace Project.Smalltalk.SelectedReturnHeap
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.Graph Project.Smalltalk.PointerTypes Project.Smalltalk.Reachability

theorem selected_valid {s : Array UInt64} {cap : Nat} {target : UInt64}
    (valid : Heap.Valid s cap) (typed : PointerTypes.Valid s cap) (phase : read s 0 ≠ 4)
    (activation : kind s (read s 2) = 5) (targetTag : kind s target = 5)
    (reached : Reachable s target) (stackCell : kind s (field s (read s 2) 7) = 7) :
    Heap.Valid (returnReserved s target (field s target 4) (field s (field s (read s 2) 7) 2)) cap ∧
    PointerTypes.Valid (returnReserved s target (field s target 4) (field s (field s (read s 2) 7) 2)) cap := by
  have targetFacts := reachable_allocated valid.1 reached
  have tag : field s target 0 = 5 := (kind_eq_field valid.1.1 targetFacts.1).symm.trans targetTag
  have callerType := typed target targetFacts.1 targetFacts.2 4 (by decide) 5 (by rw [tag]; simp [Required])
  have callerLive := pointer_live reached (show (4 : UInt64).toNat < 8 by decide) (by
    rw [tag]; simp [PointerField])
  have valueLive := InstructionHeap.top_live valid.1 activation stackCell
  exact ReturnHeap.returnReserved_valid (stop := target) (caller := field s target 4)
    (value := field s (field s (read s 2) 7) 2) valid typed phase activation callerType callerLive valueLive

end Project.Smalltalk.SelectedReturnHeap
