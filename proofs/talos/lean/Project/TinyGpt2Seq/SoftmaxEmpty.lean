import Project.TinyGpt2Seq.SoftmaxCode

namespace Project.TinyGpt2Seq.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution Project.SequenceSoftmax.Spec

def softmaxEmptySaved (ptr : UInt64) : List Value :=
  List.replicate 21 (.i64 0) ++ [.i64 ptr, .i64 0, .i64 0, .i64 0]

theorem softmax_empty_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner : UInt64) (source : FreeNode) (remaining pageLimit : Nat)
    (hHeap : heap.At initial) (hInput : heap.OwnsWords initial source #[])
    (hBudget : OutputBudget initial heap (computeBytes 0+remaining) pageLimit module) :
    TerminatesWith env module 49 initial [.i64 source.root, .i64 owner]
      (SoftmaxPost heap initial #[] remaining pageLimit) := by
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
  refine TerminatesWith.of_wp_entry_for (f := func49Def) rfl ?_ (by decide)
  change wp module func49 _ initial (func49Def.toLocals [.i64 owner, .i64 source.root]) env
  rw [softmax_shape]
  simp only [func49, List.take, List.cons_append, List.nil_append]
  wp_fixed_frame [func49Def]
  simp [hInput.buffer.values.pointerAddress_eq, hInput.buffer.values.lengthRead,
    hInput.buffer.values.generatedLengthBound]
  try simp only [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp)]
  wp_fixed_frame
  try simp only [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp)]
  wp_fixed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp)]
  unfold softmaxEmpty
  simp only [List.append_assoc]
  apply FixedArrayCapacity.constantProgram_spec 0 1 27 module env initial _ rfl
    (by change 2 ≤ 27; decide) (by change 27 < 33; decide)
  change wp module _ _ initial
    (FixedArraySearch.frame [.i64 owner, .i64 source.root] (softmaxEmptySaved source.root) []
      8 0 0 0 0 0) env
  apply FixedArrayAllocate.program_spec module env initial [.i64 owner, .i64 source.root]
    (softmaxEmptySaved source.root) [] 27 rfl
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
    wp_fixed_frame [FixedArraySearch.frame, softmaxEmptySaved, List.replicate, List.append]
    apply FixedArrayResult.lengthStore_spec module env (mapAllocated heap initial 0) _
      (mapRoot heap 0) 0 23 rfl rfl
    · rw [ProofKit.Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
      exact hBounds.2
    · wp_fixed_frame [func49Def]
      refine ⟨heap.allocate 8, allocatedNode heap.top 8 heap.nodes, rfl,
        hFinished.1, ?_, hFinished.2.2.1, hFinished.2.2.2⟩
      exact hFinished.2.1

#print axioms softmax_empty_exact
end Project.TinyGpt2Seq.Spec
