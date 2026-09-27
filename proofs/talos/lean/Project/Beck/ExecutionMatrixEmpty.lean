import Project.Beck.ExecutionMatrixOuterLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def matrixInitialSaved (root previous : UInt64) (k : Fin 63) : Value :=
  match k.val with
  | 2 => .i64 root
  | 61 => .i64 8
  | 62 => .i64 previous
  | _ => .i64 0

def matrixInitialTail (root current capacity next : UInt64) (k : Fin 15) : UInt64 :=
  match k.val with
  | 0 => current
  | 1 => capacity
  | 2 => next
  | 3 => root
  | _ => 0

set_option maxRecDepth 2048 in
theorem matrix_empty_shape : func19.take 53 = FixedArrayCapacity.constantProgram 0 1 70 ++
    FixedArrayAllocate.program 70 1 ++ (func19.drop 33).take 20 := rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1500000 in
theorem matrixEmpty_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64) (remaining pageLimit : Nat)
    (valid : heap.At initial) (budget : OutputBudget initial heap (56 + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (finish : let final := emptyWords heap initial
      let node := allocatedNode heap.top 8 heap.nodes
      (heap.allocate 8).At final → (heap.allocate 8).OwnsWords final node #[] →
      heap.Frame initial (heap.allocate 8) final →
      OutputBudget final (heap.allocate 8) remaining pageLimit Project.Beck.«module» →
      ∀ previous current capacity next,
      wp Project.Beck.«module» rest Q final
        (matrixOuterFrame input point inputOwner inputPointer pointOwner pointPointer 0 node.root node.root
          (matrixInitialSaved node.root previous) (matrixInitialTail node.root current capacity next) (fun _ => .i64 0)) env) :
    wp Project.Beck.«module» (func19.take 53 ++ rest) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
        locals := List.replicate 89 (.i64 0) } env := by
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
  rw [matrix_empty_shape]
  simp only [List.append_assoc, FixedArrayCapacity.constantProgram, List.cons_append, List.nil_append]
  wp_fixed_frame [matrixParams, inputValues, pointValues]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide), wp_nil]
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  change wp Project.Beck.«module» (FixedArrayAllocate.program 70 1 ++ _) Q initial
    (FixedArraySearch.frame (matrixParams input point inputOwner inputPointer pointOwner pointPointer)
      (List.replicate 61 (.i64 0)) (List.replicate 22 (.i64 0)) 8 0 0 0 0 0) env
  apply allocation_exact env initial heap _ _ _ 70 (by simp [matrixParams, inputValues, pointValues]) 8 0 0 0 0 0 valid
    (fun h => ⟨(space h).1.le, by simpa only [FixedArrayBump.requiredPages, bumpPages] using (space h).2⟩)
    (budget.pages.trans budget.pageLimitBound)
  intro previous current capacity next
  simp only [func19, List.drop, List.take, FixedArraySearch.frame, matrixParams, inputValues, pointValues,
    List.reverse_cons, List.reverse_nil, List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append]
  wp_fixed_frame_step
  wp_fixed_frame_step
  refine FixedArrayResult.lengthStore_spec Project.Beck.«module» env _ _
    (allocatedRoot heap.top 8 heap.nodes) 0 66 rfl rfl memory _ _ ?_
  wp_fixed_frame
  simpa only [matrixOuterFrame, matrixPlainFrame, matrixOuterSaved, matrixParams, matrixPrefix, matrixTail, matrixSuffix,
    matrixInitialSaved, matrixInitialTail, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
    List.cons_append, List.nil_append, emptyWords, allocatedNode, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.toUInt64, show UInt64.ofNat 0 = 0 by decide, reduceIte] using
    finish allocatedValid owned preserved finalBudget previous current capacity next

#print axioms matrixEmpty_exact

end Project.Beck.Execution
