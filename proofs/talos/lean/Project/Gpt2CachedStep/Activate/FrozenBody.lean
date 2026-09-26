import Project.Gpt2CachedStep.Activate.FrozenSize
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2CachedStep.Frozen.Activate
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2

def need (input : ByteArray) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (4 * (input.size / 4)))

set_option maxRecDepth 32768 in
theorem emitted_body : func32 = func32.take 18 ++ PackedCapacity.program 15 17 ++
    PackedAllocation.program 17 ++ [.localGet 22, .localSet 16, .constI64 0, .localSet 4] ++
    (func32.drop 49).take 1 ++ func32.drop 50 := rfl

set_option maxRecDepth 32768 in
theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (inputOwner inputPtr : UInt64) (input : ByteArray) (frame : Locals)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hBump : takeFirstFitFrom 0 (need input) heap.nodes = none →
      heap.top.toNat + 48 + (need input).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need input) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters inputOwner inputPtr input)
    (hLocals : frame.locals.length = 20) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      result.values = [.i64 (UInt64.ofNat (activate input).size),
        .i64 (allocatedRoot heap.top (need input) heap.nodes),
        .i64 (allocatedRoot heap.top (need input) heap.nodes)] →
      heap.PackedOutput initial final (need input) (activate input) →
      wp «module» rest Q final result env) :
    wp «module» (func32 ++ rest) Q initial frame env := by
  have hCount : 4 * (input.size / 4) ≤ 2^32 := by have := hInput.1; omega
  have hOutputSize : (activate input).size = 4 * (input.size / 4) := PackedSource.generate_size _ _
  have hParamLength : frame.params.length = 3 := by rw [hParams]; rfl
  have hCapacity : (need input).toNat = PackedCapacity.capacityNat (4 * (input.size / 4)) :=
    PackedCapacity.capacity_toNat _ hCount
  have hNeed : 4 * (input.size / 4) ≤ (need input).toNat := by
    rw [hCapacity]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (need input) hHeap hBound
  have hInputAllocated := hAllocFrame.packed hInputProtected hInput
  have hBounds := PackedAllocation.root_bounds initial heap.top (need input) heap.nodes hHeap.freeList hBound
  have hSep := hInputProtected.allocated_disjoint (need input) hBound
  have hSpace := allocated_capacity (need input) heap.nodes
  rw [emitted_body]
  simp only [List.append_assoc]
  apply size_spec env initial frame input hParamLength hLocals hValues
    (by rw [hParams]; rfl) (by have := hInput.1; omega)
  apply PackedCapacity.program_spec 15 17 (UInt64.ofNat (4 * (input.size / 4))) «module» env initial
    (sizeFrame frame input)
  · simp [sizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [sizeFrame, hParamLength]
  · simp [sizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (sizeFrame frame input) 17 (need input)
  have hPreparedParams : prepared.params = frame.params := by simp [prepared, FixedArrayCapacity.capacityFrame, sizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 20 := by simp [prepared, FixedArrayCapacity.capacityFrame, sizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      sizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 17 heap.top
    (need input) heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]
  · simp [prepared, FixedArrayCapacity.capacityFrame, sizeFrame, Locals.get, hParamLength, hLocals]
  · rw [hHeap.globals]; rfl
  · rw [hHeap.globals]; rfl
  · rw [hHeap.globals]; rfl
  · exact hHeap.freeList
  · exact fun h => ⟨(hBump h).1.le, (hBump h).2⟩
  · exact hPages
  · rfl
  intro previous current capacity next
  simp only [List.cons_append, List.nil_append]
  wp_packed_frame [PackedAllocation.allocatedFrame, FixedArraySearch.frame, hPreparedParams,
    hPreparedLocals, hParamLength, List.length_append, List.length_take, List.length_drop,
    List.getElem?_append, List.getElem?_take, show min 14 20 = 14 from rfl]
  apply loop_spec env (heap.allocatePackedStore initial (need input))
    inputOwner inputPtr (allocatedRoot heap.top (need input) heap.nodes) input _ hInputAllocated
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · simp [PackedGenerateLoop.Ready,
      prepared, FixedArrayCapacity.capacityFrame, sizeFrame, Locals.get, Locals.validIndex,
      hParams, parameters, hLocals]
    rfl
  · simp (config := { maxDischargeDepth := 64 }) [State,
      prepared,
      FixedArrayCapacity.capacityFrame, sizeFrame, hParams, parameters, hLocals,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final (need input) (activate input) hHeap
    (by rw [hOutputSize]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [hOutputSize]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[13]? = some (.i64 (allocatedRoot heap.top (need input) heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  simp only [parameters] at hResultParams
  simp only [func32, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hResultParams, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · rw [hOutputSize]
  · exact hOutput

#print axioms body_spec

end Project.Gpt2CachedStep.Frozen.Activate
