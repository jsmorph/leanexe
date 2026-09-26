import Project.Beck.ExecutionInputFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem inputEmpty_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (pointer : UInt64) (saved : InputSaved) (tail : InputTail) (destination : Nat)
    (destinationBound : destination = 25 ∨ destination = 26) (remaining pageLimit : Nat)
    (valid : heap.At initial) (budget : OutputBudget initial heap (56 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : let final := emptyWords heap initial
      let node := allocatedNode heap.top 8 heap.nodes
      (heap.allocate 8).At final → (heap.allocate 8).OwnsWords final node #[] →
      heap.Frame initial (heap.allocate 8) final →
      OutputBudget final (heap.allocate 8) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (inputFrame pointer (inputEmptySaved saved destination node.root)
          (inputEmptyTail tail node.root previous current capacity next)) env) :
    wp Project.Beck.«module» (inputEmptyProgram destination ++ rest) Q initial (inputFrame pointer saved tail) env := by
  have space := budget.bump 8 (by change 48 + 8 ≤ 56 + remaining; omega)
  have bounds := emptyWords_bounds heap initial valid (fun h => (space h).1.le)
  have memory : (allocatedRoot heap.top 8 heap.nodes).toUInt32.toNat + 8 ≤
      (heap.allocateArrayStore initial 8 1).mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    exact bounds.2
  obtain ⟨allocatedValid, owned⟩ := emptyWords_owned heap initial valid (fun h => (space h).1)
  have preserved := emptyWords_frame heap initial valid (fun h => (space h).1.le)
  have writes := Project.EulerRiemann.Memory.writeLength_frame (heap.allocateArrayStore initial 8 1)
    (allocatedRoot heap.top 8 heap.nodes) 0 bounds.1
  have finalBudget := budget.allocated 8 1 remaining (by change 56 + remaining ≤ 56 + remaining; omega) writes
  dsimp only at finish
  simp only [inputEmptyProgram, List.append_assoc, FixedArrayCapacity.constantProgram,
    inputFrame, inputPrefix, List.cons_append, List.nil_append]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide), wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 56 1 ++ _) Q initial
    (FixedArraySearch.frame [.i64 pointer, .i64 pointer]
      (inputPrefix saved ++ [.i64 (tail 0), .i64 (tail 1), .i64 (tail 2), .i64 (tail 3)])
      [] 8 (tail 5) (tail 6) (tail 7) (tail 8) (tail 9)) env
  apply allocation_exact env initial heap _ _ [] 56 rfl 8 (tail 5) (tail 6) (tail 7) (tail 8) (tail 9) valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous current capacity next
  simp only [FixedArraySearch.frame, inputPrefix, List.cons_append, List.nil_append]
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine FixedArrayResult.lengthStore_spec Project.Beck.«module» env _ _
    (allocatedRoot heap.top 8 heap.nodes) 0 52 rfl rfl memory _ _ ?_
  rcases destinationBound with rfl | rfl
  all_goals
    wp_fixed_frame
    simpa only [inputFrame, inputPrefix, inputEmptySaved, inputEmptyTail, emptyWords, allocatedNode,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, or_false, false_or, reduceIte,
      List.cons_append, List.nil_append] using
      finish allocatedValid owned preserved finalBudget previous current capacity next

#print axioms inputEmpty_exact

end Project.Beck.Execution
