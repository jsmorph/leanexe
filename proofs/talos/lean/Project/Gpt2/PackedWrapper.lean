import Project.Gpt2.PackedCall
import Project.ProofKit.PackedAllocExport

/-! The actual instruction sequence emitted by packed-module.js for the
linear wrapper. Allocation runs in Wasm before the synchronous host call.
The host hypothesis specifies completed shader execution and byte transfer,
not equality to the parent matrix operation. The shader certificate supplies
that equality. This theorem alone does not establish the full hybrid session. -/
namespace Project.Gpt2.PackedWrapper
open Wasm LeanExe.WGSL Project.ProofKit Project.EulerRiemann.Execution

def linear : Wasm.Function :=
  { params := List.replicate 11 .i64, locals := [.i64], results := [.i64, .i64, .i64],
    typeIdx := some 21,
    body := [.localGet 9, .constI64 4, .mulI64, .call 41, .localSet 11,
      .localGet 0, .localGet 1, .localGet 2, .localGet 3, .localGet 4, .localGet 5,
      .localGet 6, .localGet 7, .localGet 8, .localGet 9, .localGet 10, .localGet 11,
      .call 0, .localGet 11, .localGet 11, .localGet 9, .constI64 4, .mulI64] }

def qkvParameters (weightsOwner weightsPtr inputOwner inputPtr : UInt64)
    (weights input : ByteArray) (weightOffset biasOffset : UInt64) : List Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
   .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size),
   .i64 weightOffset, .i64 biasOffset, .i64 768, .i64 2304, .i64 1]

theorem qkv_exact (module_ : Wasm.Module) (env : HostEnv Unit)
    (hWrapper : module_.funcs[23 - module_.imports.length]? = some linear)
    (hNotImport : module_.imports[23]? = none)
    (hAlloc : module_.funcs[41 - module_.imports.length]? = some (PackedAllocExport.function (some 39)))
    (hAllocImport : module_.imports[41]? = none) (hMemory : module_.memIs64 = false)
    (imp : ImportDecl) (host : HostFn Unit)
    (hImp : module_.imports[0]? = some imp) (hHost : env.funcs[0]? = some host)
    (hParams : imp.params = List.replicate 12 .i64) (hResults : imp.results = [])
    (text : String)
    (checked : Statement.Implements text ⟨1, 2304, 768, 768 * 2304 + 2304⟩
      (Gpt2Packed.biased 768 2304))
    (initial : Store Unit) (heap : Heap) (hHeap : heap.At initial)
    (weightsOwner weightsPtr inputOwner inputPtr : UInt64)
    (weights input : ByteArray) (weightOffset biasOffset : UInt64)
    (hBump : Project.Runtime.takeFirstFitFrom 0 9216 heap.nodes = none →
      heap.top.toNat + 48 + 9216 < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top 9216 ≤ initial.memoryCap module_ 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hCompleted : host.invoke (heap.allocatePackedStore initial 9216)
        (qkvParameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset ++
          [.i64 (allocatedRoot heap.top 9216 heap.nodes)]) =
      .Return [] (PackedCall.complete heap initial 9216
        (PackedBody.biasedBytes text weights input weightOffset.toNat biasOffset.toNat 768 2304))) :
    TerminatesWith env module_ 23 initial
      (qkvParameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset).reverse
      (fun final values =>
        values = [.i64 9216, .i64 (allocatedRoot heap.top 9216 heap.nodes),
          .i64 (allocatedRoot heap.top 9216 heap.nodes)] ∧
        heap.PackedOutput initial final 9216
          (LeanExe.Models.Gpt2.linearRows weights input weightOffset.toNat biasOffset.toNat 768 2304 1)) := by
  have hAllocate := PackedAllocExport.exact module_ env 41 initial heap.top 9216 heap.allocations heap.nodes
    hAlloc hAllocImport (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl)
    (by rw [hHeap.globals]; rfl) hHeap.freeList
    (fun h => ⟨(hBump h).1.le, (hBump h).2⟩) hPages hMemory
  have hOutput := PackedCall.biased_contract text 768 2304 checked weights input
    weightOffset.toNat biasOffset.toNat (by decide) heap initial 9216 hHeap (by decide)
    (fun h => (hBump h).1) hPages
  refine TerminatesWith.of_wp_entry_for hWrapper ?_ hNotImport
  wp_packed_frame [linear, qkvParameters, Function.toLocals, Function.numParams]
  refine wp_call_tw hAllocate ?_
  rintro allocated values ⟨rfl, rfl⟩
  wp_packed_frame [linear, qkvParameters, Function.numParams]
  refine wp_call_host_cons hImp hHost ?_ ?_ ?_
  · intro values final hReturn
    simp only [hParams] at hReturn
    change host.invoke (heap.allocatePackedStore initial 9216)
      (qkvParameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset ++
        [.i64 (allocatedRoot heap.top 9216 heap.nodes)]) = .Return values final at hReturn
    rw [hCompleted] at hReturn
    cases hReturn
    wp_packed_frame [hParams, hResults, linear, qkvParameters, Function.numParams]
    simpa [List.take, List.drop, List.reverse_cons, List.reverse_nil, List.set,
      show PackedAllocation.root heap.top (PackedCapacity.capacity 9216) heap.nodes =
        allocatedRoot heap.top 9216 heap.nodes from rfl] using hOutput
  · intro final message hTrap
    simp only [hParams] at hTrap
    change host.invoke (heap.allocatePackedStore initial 9216)
      (qkvParameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset ++
        [.i64 (allocatedRoot heap.top 9216 heap.nodes)]) = .Trap final message at hTrap
    rw [hCompleted] at hTrap
    cases hTrap
  · intro final tag arguments hThrow
    simp only [hParams] at hThrow
    change host.invoke (heap.allocatePackedStore initial 9216)
      (qkvParameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset ++
        [.i64 (allocatedRoot heap.top 9216 heap.nodes)]) = .Throw final tag arguments at hThrow
    rw [hCompleted] at hThrow
    cases hThrow

#print axioms qkv_exact
end Project.Gpt2.PackedWrapper
