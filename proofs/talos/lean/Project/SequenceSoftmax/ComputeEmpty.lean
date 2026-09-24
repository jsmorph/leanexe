import Project.SequenceSoftmax.ComputeState
import Project.SequenceSoftmax.AnnotationMatches

namespace Project.SequenceSoftmax.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution AnnotationMatches

def emptyProgram : Wasm.Program :=
  FixedArrayCapacity.constantProgram 0 1 26 ++ FixedArrayAllocate.program 26 1 ++
  [.localGet 31, .localSet 22] ++ FixedArrayResult.lengthStoreProgram 22 0 ++
  [.localGet 22, .localSet 1, .localGet 1, .localSet 20, .localGet 1, .localSet 21]

theorem empty_shape : function_11_length_dispatch_0_valid_branch_program = emptyProgram := rfl

def emptySaved (ptr : UInt64) : List Value :=
  List.replicate 21 (.i64 0) ++ [.i64 ptr, .i64 0, .i64 0, .i64 0]

theorem compute_empty_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (source : FreeNode) (remaining pageLimit : Nat)
    (hHeap : heap.At initial) (hInput : heap.OwnsWords initial source #[])
    (hBudget : OutputBudget initial heap (computeBytes 0+remaining) pageLimit module) :
    TerminatesWith env module 11 initial [.i64 source.root]
      (ComputePost heap initial #[] remaining pageLimit) := by
  have hBudget0 : OutputBudget initial heap (56+remaining) pageLimit module :=
    hBudget.mono (by simp only [computeBytes]; omega)
  have hBump := hBudget0.bump 8 (by change 48+8 ≤ 56+remaining; omega)
  have hBounds := heap.allocate_word_bounds initial 8 1 0 hHeap (by decide) (fun h => (hBump h).1.le)
  change (mapRoot heap 0).toNat+8 ≤ 4294967296 ∧
    (mapRoot heap 0).toNat+8 ≤ (mapAllocated heap initial 0).mem.pages*65536 at hBounds
  obtain ⟨hPrefix, _, _, hWrites⟩ := map_initialize heap initial source #[] #[] hHeap hInput rfl
    (fun h => (hBump h).1.le)
  have hFinished := map_finish module heap initial (mapInitialized heap initial 0) #[] remaining pageLimit
    hHeap hBudget0 rfl (UInt64Array.PrefixAt.complete hPrefix) hWrites
  refine TerminatesWith.of_wp_entry_for (f := func11Def) rfl ?_ (by decide)
  change wp module func11 _ initial (func11Def.toLocals [.i64 source.root]) env
  rw [function_11_length_dispatch_0_function_eq]
  unfold function_11_length_dispatch_0_dispatch_program
  apply FixedArrayLengthDispatch.eqProgram_spec (booleanResults := [.i64]) 22 0 _ _ _ module env initial
    _ source.root #[] rfl rfl (by decide) (by change 22 < 32; decide) (by decide) hInput.buffer.values
  · intro hNonempty
    exact False.elim (hNonempty rfl)
  · intro _
    rw [empty_shape]
    unfold emptyProgram
    simp only [List.append_assoc]
    apply FixedArrayCapacity.constantProgram_spec 0 1 26 module env initial _ rfl
      (by change 1 ≤ 26; decide) (by change 26 < 32; decide)
    change wp module _ _ initial
      (FixedArraySearch.frame [.i64 source.root] (emptySaved source.root) []
        8 0 0 0 0 0) env
    apply FixedArrayAllocate.program_spec module env initial [.i64 source.root]
      (emptySaved source.root) [] 26 rfl
      heap.top 8 1 0 0 0 0 0 heap.allocations heap.nodes
    · simp [hHeap.globals, Heap.globals]
    · simp [hHeap.globals, Heap.globals]
    · simp [hHeap.globals, Heap.globals]
    · exact hHeap.freeList
    · exact fun h => ⟨(hBump h).1.le, (hBump h).2⟩
    · exact hBudget.pages.trans hBudget.pageLimitBound
    · rfl
    · intro previous current capacity next
      simp only [List.cons_append, List.nil_append]
      wp_fixed_frame [FixedArraySearch.frame, emptySaved, List.replicate, List.append]
      apply FixedArrayResult.lengthStore_spec module env (mapAllocated heap initial 0) _
        (mapRoot heap 0) 0 22 rfl rfl
      · rw [ProofKit.Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
        exact hBounds.2
      · wp_fixed_frame [FixedArrayEqNode.branchPost, function_11_length_dispatch_0_suffix_program, func11Def]
        refine ⟨heap.allocate 8, allocatedNode heap.top 8 heap.nodes, rfl,
          hFinished.1, ?_, hFinished.2.2.1, hFinished.2.2.2⟩
        exact hFinished.2.1

#print axioms empty_shape
#print axioms compute_empty_exact
end Project.SequenceSoftmax.Spec
