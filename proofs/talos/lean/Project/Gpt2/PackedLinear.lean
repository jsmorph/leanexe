import Project.Gpt2.PackedWrapper

/-! The linear wrapper contract for any certified one-row biased product.
Concrete model shapes supply their own checked shader certificates. -/
namespace Project.Gpt2.PackedLinear
open Wasm LeanExe.WGSL Project.ProofKit Project.EulerRiemann.Execution

def bytes (cols : Nat) : UInt64 := UInt64.ofNat (4 * cols)
def need (cols : Nat) : UInt64 := PackedCapacity.capacity (bytes cols)
def parameters (weightsOwner weightsPtr inputOwner inputPtr : UInt64)
    (weights input : ByteArray) (weightOffset biasOffset : UInt64) (inner cols : Nat) : List Value :=
  [.i64 weightsOwner, .i64 weightsPtr, .i64 (UInt64.ofNat weights.size),
   .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size),
   .i64 weightOffset, .i64 biasOffset, .i64 (UInt64.ofNat inner), .i64 (UInt64.ofNat cols), .i64 1]

theorem exact (module_ : Wasm.Module) (env : HostEnv Unit)
    (hWrapper : module_.funcs[23 - module_.imports.length]? = some PackedWrapper.linear)
    (hNotImport : module_.imports[23]? = none)
    (hAlloc : module_.funcs[41 - module_.imports.length]? = some (PackedAllocExport.function (some 39)))
    (hAllocImport : module_.imports[41]? = none) (hMemory : module_.memIs64 = false)
    (imp : ImportDecl) (host : HostFn Unit)
    (hImp : module_.imports[0]? = some imp) (hHost : env.funcs[0]? = some host)
    (hParams : imp.params = List.replicate 12 .i64) (hResults : imp.results = [])
    (text : String) (inner cols : Nat)
    (checked : Statement.Implements text ⟨1, cols, inner, inner * cols + cols⟩ (Gpt2Packed.biased inner cols))
    (hCount : 4 * cols ≤ 4294967296)
    (initial : Store Unit) (heap : Heap) (hHeap : heap.At initial)
    (weightsOwner weightsPtr inputOwner inputPtr : UInt64)
    (weights input : ByteArray) (weightOffset biasOffset : UInt64)
    (hBump : Project.Runtime.takeFirstFitFrom 0 (need cols) heap.nodes = none →
      heap.top.toNat + 48 + (need cols).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need cols) ≤ initial.memoryCap module_ 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hCompleted : host.invoke (heap.allocatePackedStore initial (need cols))
        (parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset inner cols ++
          [.i64 (allocatedRoot heap.top (need cols) heap.nodes)]) =
      .Return [] (PackedCall.complete heap initial (need cols)
        (PackedBody.biasedBytes text weights input weightOffset.toNat biasOffset.toNat inner cols))) :
    TerminatesWith env module_ 23 initial
      (parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset inner cols).reverse
      (fun final values =>
        values = [.i64 (bytes cols), .i64 (allocatedRoot heap.top (need cols) heap.nodes),
          .i64 (allocatedRoot heap.top (need cols) heap.nodes)] ∧
        heap.PackedOutput initial final (need cols)
          (LeanExe.Models.Gpt2.linearRows weights input weightOffset.toNat biasOffset.toNat inner cols 1)) := by
  have hMultiply : UInt64.ofNat cols * 4 = bytes cols := by
    change UInt64.ofNat cols * UInt64.ofNat 4 = UInt64.ofNat (4 * cols)
    rw [← UInt64.ofNat_mul, Nat.mul_comm cols 4]
  have hSpace : 4 * cols ≤ (need cols).toNat := by
    rw [need, bytes, PackedCapacity.capacity_toNat _ hCount]
    exact PackedCapacity.capacityNat_ge _
  have hAllocate := PackedAllocExport.exact module_ env 41 initial heap.top (bytes cols) heap.allocations heap.nodes
    hAlloc hAllocImport (by rw [hHeap.globals]; rfl) (by rw [hHeap.globals]; rfl)
    (by rw [hHeap.globals]; rfl) hHeap.freeList
    (fun h => ⟨(hBump h).1.le, (hBump h).2⟩) hPages hMemory
  have hOutput := PackedCall.biased_contract text inner cols checked weights input
    weightOffset.toNat biasOffset.toNat (by omega) heap initial (need cols) hHeap hSpace
    (fun h => (hBump h).1) hPages
  refine TerminatesWith.of_wp_entry_for hWrapper ?_ hNotImport
  wp_packed_frame [PackedWrapper.linear, parameters, Function.toLocals, Function.numParams, hMultiply]
  change wp module_ _ _ initial
    { params := parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset inner cols,
      locals := [.i64 0], values := [.i64 (UInt64.ofNat cols * 4)] } env
  simp only [hMultiply]
  refine wp_call_tw hAllocate ?_
  rintro allocated values ⟨rfl, rfl⟩
  wp_packed_frame [PackedWrapper.linear, parameters, Function.numParams]
  refine wp_call_host_cons hImp hHost ?_ ?_ ?_
  · intro values final hReturn
    simp only [hParams] at hReturn
    change host.invoke (heap.allocatePackedStore initial (need cols))
      (parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset inner cols ++
        [.i64 (allocatedRoot heap.top (need cols) heap.nodes)]) = .Return values final at hReturn
    rw [hCompleted] at hReturn
    cases hReturn
    wp_packed_frame [hParams, hResults, PackedWrapper.linear, parameters, Function.numParams]
    simpa [List.take, List.drop, List.reverse_cons, List.reverse_nil, List.set, hMultiply,
      show PackedAllocation.root heap.top (PackedCapacity.capacity (bytes cols)) heap.nodes =
        allocatedRoot heap.top (need cols) heap.nodes from rfl] using hOutput
  · intro final message hTrap
    simp only [hParams] at hTrap
    change host.invoke (heap.allocatePackedStore initial (need cols))
      (parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset inner cols ++
        [.i64 (allocatedRoot heap.top (need cols) heap.nodes)]) = .Trap final message at hTrap
    rw [hCompleted] at hTrap
    cases hTrap
  · intro final tag arguments hThrow
    simp only [hParams] at hThrow
    change host.invoke (heap.allocatePackedStore initial (need cols))
      (parameters weightsOwner weightsPtr inputOwner inputPtr weights input weightOffset biasOffset inner cols ++
        [.i64 (allocatedRoot heap.top (need cols) heap.nodes)]) = .Throw final tag arguments at hThrow
    rw [hCompleted] at hThrow
    cases hThrow

#print axioms exact
end Project.Gpt2.PackedLinear
