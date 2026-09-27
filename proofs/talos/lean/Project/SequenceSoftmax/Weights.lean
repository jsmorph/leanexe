import Project.SequenceSoftmax.WeightsMap
import Project.SequenceSoftmax.Allocation
import Project.ProofKit.ExactCall
import Project.ProofKit.FixedFrame

namespace Project.SequenceSoftmax.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution
  UInt64Array ProofKit.Memory

def weightsProgram : Wasm.Program :=
  [.localGet 1, .localSet 9, .localGet 9, .wrapI64, .load64 0, .localSet 10] ++
  FixedArrayCapacity.localProgram 10 1 15 ++ FixedArrayAllocate.program 15 1 ++
  [.localGet 20, .localSet 11] ++ FixedArrayResult.lengthStoreLocalProgram 11 10 ++
  [.constI64 0, .localSet 12, .block 0 0 [.loop 0 0 weightsMapBody]] ++
  [.localGet 11, .localSet 6, .localGet 6, .localSet 7, .localGet 6, .localSet 8,
   .localGet 7, .localGet 8]

theorem weights_shape : func6 = weightsProgram := rfl

theorem weights_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner maximum : UInt64) (source : FreeNode) (input : Array UInt64)
    (hHeap : heap.At initial) (hInput : heap.OwnsWords initial source input)
    (hBump : takeFirstFitFrom 0 (mapCapacity input.size) heap.nodes = none →
      heap.top.toNat+48+(mapCapacity input.size).toNat ≤ 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (mapCapacity input.size) ≤ initial.memoryCap module 0)
    (hPages : initial.mem.pages ≤ 65536) :
    TerminatesWith env module 6 initial [.i64 maximum, .i64 source.root, .i64 owner]
      (fun final values => values = [.i64 (mapRoot heap input.size), .i64 (mapRoot heap input.size)] ∧
        At final (mapRoot heap input.size) (weights input maximum) ∧
        WritesRange (mapAllocated heap initial input.size) final (mapRoot heap input.size).toNat
          ((mapRoot heap input.size).toNat+8*(input.size+1))) := by
  have hCapacity := map_capacity initial source.root input hInput.buffer.values
  have hBounds := heap.allocate_word_bounds initial (mapCapacity input.size) 1 input.size
    hHeap (by omega) (fun h => (hBump h).1)
  change (mapRoot heap input.size).toNat+8*(input.size+1) ≤ 4294967296 ∧
    (mapRoot heap input.size).toNat+8*(input.size+1) ≤
      (mapAllocated heap initial input.size).mem.pages*65536 at hBounds
  obtain ⟨hPrefix, hInitializedInput, hDisjoint, hLengthWrites⟩ :=
    map_initialize heap initial source input (weights input maximum) hHeap hInput
      (by simp [weights]) (fun h => (hBump h).1)
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_ (by decide)
  change wp module func6 _ initial (func6Def.toLocals [.i64 owner, .i64 source.root, .i64 maximum]) env
  rw [weights_shape]
  unfold weightsProgram
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_fixed_frame [func6Def]
  simp [hInput.buffer.values.pointerAddress_eq, hInput.buffer.values.lengthRead,
    hInput.buffer.values.generatedLengthBound]
  apply FixedArrayCapacity.localProgram_spec 10 (UInt64.ofNat input.size) 1 15
    module env initial _ rfl rfl (by change 3 ≤ 15; decide) (by change 15 < 21; decide)
  rw [hCapacity.2]
  change wp module _ _ initial
    (FixedArraySearch.frame [.i64 owner, .i64 source.root, .i64 maximum]
      (weightsMapFrame owner source.root maximum 0 input.size 0 0 0 0 []).locals []
      (mapCapacity input.size) 0 0 0 0 0) env
  apply FixedArrayAllocate.program_spec module env initial
    [.i64 owner, .i64 source.root, .i64 maximum]
    (weightsMapFrame owner source.root maximum 0 input.size 0 0 0 0 []).locals [] 15 rfl
    heap.top (mapCapacity input.size) 1 0 0 0 0 0 heap.allocations heap.nodes
  · simp [hHeap.globals, Heap.globals]
  · simp [hHeap.globals, Heap.globals]
  · simp [hHeap.globals, Heap.globals]
  · exact hHeap.freeList
  · exact hBump
  · exact hPages
  · rfl
  · intro previous current capacity next
    wp_fixed_frame [FixedArraySearch.frame, weightsMapFrame]
    apply FixedArrayResult.lengthStoreLocal_spec module env
      (mapAllocated heap initial input.size) _ (mapRoot heap input.size) (UInt64.ofNat input.size) 11 10 rfl rfl
    · rw [ProofKit.Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by change (mapRoot heap input.size).toNat < 4294967296; omega)]
      exact le_trans (by omega) hBounds.2
    · wp_fixed_frame
      change wp module ([.block 0 0 [.loop 0 0 weightsMapBody]] ++ _) _
        (mapInitialized heap initial input.size)
        (weightsMapFrame owner source.root maximum (mapRoot heap input.size) input.size 0 0 0 0
          [.i64 (mapCapacity input.size), .i64 previous, .i64 current, .i64 capacity,
           .i64 next, .i64 (mapRoot heap input.size)]) env
      apply weightsMap_program_spec env _ owner source.root maximum (mapRoot heap input.size)
        input _ hInitializedInput hDisjoint hPrefix
      intro final last argument result hOutput hWrites
      wp_fixed_frame [weightsMapFrame]
      exact ⟨rfl, hOutput, hLengthWrites.trans hWrites⟩

#print axioms weights_shape
#print axioms weights_exact
end Project.SequenceSoftmax.Spec
