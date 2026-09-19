import Project.Gpt2.PackedWrapper

/-! Execution of the real vocabulary wrapper and composition of both checked
shader halves. Wasm allocates the rounded capacity and returns the byte length. -/
namespace Project.Gpt2.PackedVocabulary
open Wasm LeanExe.WGSL Project.ProofKit Project.EulerRiemann.Execution

def wrapper : Wasm.Function :=
  { params := List.replicate 6 .i64, locals := [.i64], results := [.i64, .i64, .i64],
    typeIdx := some 37,
    body := [.constI64 201028, .call 41, .localSet 6,
      .localGet 0, .localGet 1, .localGet 2, .localGet 3, .localGet 4, .localGet 5, .localGet 6,
      .call 1, .localGet 6, .localGet 6, .constI64 201028] }

def parameters (weightsOwner weightsPtr inputOwner inputPtr : UInt64)
    (weights input : ByteArray) : List Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
   .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size)]

theorem exact (module_ : Wasm.Module) (env : HostEnv Unit)
    (hWrapper : module_.funcs[39 - module_.imports.length]? = some wrapper)
    (hNotImport : module_.imports[39]? = none)
    (hAlloc : module_.funcs[41 - module_.imports.length]? = some (PackedAllocExport.function (some 39)))
    (hAllocImport : module_.imports[41]? = none) (hMemory : module_.memIs64 = false)
    (imp : ImportDecl) (host : HostFn Unit)
    (hImp : module_.imports[1]? = some imp) (hHost : env.funcs[1]? = some host)
    (hParams : imp.params = List.replicate 7 .i64) (hResults : imp.results = [])
    (leftText rightText : String)
    (leftChecked : Statement.Implements leftText ⟨1, 25129, 768, 768 * 25129⟩ Matrix.Shader.vocabularyLeft.body)
    (rightChecked : Statement.Implements rightText ⟨1, 25128, 768, 768 * 25128⟩ Matrix.Shader.vocabularyRight.body)
    (initial : Store Unit) (heap : Heap) (hHeap : heap.At initial)
    (weightsOwner weightsPtr inputOwner inputPtr : UInt64) (weights input : ByteArray)
    (hBump : Project.Runtime.takeFirstFitFrom 0 201032 heap.nodes = none →
      heap.top.toNat + 48 + 201032 < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top 201032 ≤ initial.memoryCap module_ 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hCompleted : host.invoke (heap.allocatePackedStore initial 201032)
        (parameters weightsOwner weightsPtr inputOwner inputPtr weights input ++
          [.i64 (allocatedRoot heap.top 201032 heap.nodes)]) =
      .Return [] (PackedCall.complete heap initial 201032
        (PackedBody.vocabularyBytes leftText rightText weights input))) :
    TerminatesWith env module_ 39 initial
      (parameters weightsOwner weightsPtr inputOwner inputPtr weights input).reverse
      (fun final values =>
        values = [.i64 201028, .i64 (allocatedRoot heap.top 201032 heap.nodes),
          .i64 (allocatedRoot heap.top 201032 heap.nodes)] ∧
        heap.PackedOutput initial final 201032 (LeanExe.Models.Gpt2.vocabularyHead weights input)) := by
  have hAllocate := PackedAllocExport.exact module_ env 41 initial heap.top 201028 heap.allocations heap.nodes
    hAlloc hAllocImport (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl)
    (by rw [hHeap.globals]; rfl) hHeap.freeList
    (fun h => ⟨(hBump h).1.le, (hBump h).2⟩) hPages hMemory
  have hOutput := PackedCall.vocabulary_contract leftText rightText leftChecked rightChecked
    weights input heap initial 201032 hHeap (by decide) (fun h => (hBump h).1) hPages
  refine TerminatesWith.of_wp_entry_for hWrapper ?_ hNotImport
  wp_packed_frame [wrapper, parameters, Function.toLocals, Function.numParams]
  refine wp_call_tw hAllocate ?_
  rintro allocated values ⟨rfl, rfl⟩
  wp_packed_frame [wrapper, parameters, Function.numParams]
  refine wp_call_host_cons hImp hHost ?_ ?_ ?_
  · intro values final hReturn
    simp only [hParams] at hReturn
    change host.invoke (heap.allocatePackedStore initial 201032)
      (parameters weightsOwner weightsPtr inputOwner inputPtr weights input ++
        [.i64 (allocatedRoot heap.top 201032 heap.nodes)]) = .Return values final at hReturn
    rw [hCompleted] at hReturn
    cases hReturn
    wp_packed_frame [hParams, hResults, wrapper, parameters, Function.numParams]
    simpa [List.take, List.drop, List.reverse_cons, List.reverse_nil, List.set,
      show PackedAllocation.root heap.top (PackedCapacity.capacity 201028) heap.nodes =
        allocatedRoot heap.top 201032 heap.nodes from rfl] using hOutput
  · intro final message hTrap
    simp only [hParams] at hTrap
    change host.invoke (heap.allocatePackedStore initial 201032)
      (parameters weightsOwner weightsPtr inputOwner inputPtr weights input ++
        [.i64 (allocatedRoot heap.top 201032 heap.nodes)]) = .Trap final message at hTrap
    rw [hCompleted] at hTrap
    cases hTrap
  · intro final tag arguments hThrow
    simp only [hParams] at hThrow
    change host.invoke (heap.allocatePackedStore initial 201032)
      (parameters weightsOwner weightsPtr inputOwner inputPtr weights input ++
        [.i64 (allocatedRoot heap.top 201032 heap.nodes)]) = .Throw final tag arguments at hThrow
    rw [hCompleted] at hThrow
    cases hThrow

#print axioms exact
end Project.Gpt2.PackedVocabulary
