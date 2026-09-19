import Project.Gpt2CachedStep.AddRows.Size
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2CachedStep.AddRows
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2

def need (left : ByteArray) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (4 * (left.size / 4)))

set_option maxRecDepth 32768 in
theorem emitted_body : func30 = func30.take 18 ++ PackedCapacity.program 20 22 ++
    PackedAllocation.program 22 ++ [.localGet 27, .localSet 21, .constI64 0, .localSet 7] ++
    (func30.drop 49).take 1 ++ func30.drop 50 := rfl

set_option maxRecDepth 32768 in
theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (leftOwner rightOwner leftPtr rightPtr : UInt64) (left right : ByteArray) (frame : Locals)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem leftPtr.toNat left)
    (hRight : ByteArrayAt initial.mem rightPtr.toNat right)
    (hRightSize : 4 * (left.size / 4) ≤ right.size)
    (hRightProtected : heap.Protects rightPtr.toNat (rightPtr.toNat + right.size))
    (hInputProtected : heap.Protects leftPtr.toNat (leftPtr.toNat + left.size))
    (hBump : takeFirstFitFrom 0 (need left) heap.nodes = none →
      heap.top.toNat + 48 + (need left).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (need left) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters leftOwner rightOwner leftPtr rightPtr left right)
    (hLocals : frame.locals.length = 22) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      result.values = [.i64 (UInt64.ofNat (addRows left right).size),
        .i64 (allocatedRoot heap.top (need left) heap.nodes),
        .i64 (allocatedRoot heap.top (need left) heap.nodes)] →
      heap.PackedOutput initial final (need left) (addRows left right) →
      wp «module» rest Q final result env) :
    wp «module» (func30 ++ rest) Q initial frame env := by
  have hCount : 4 * (left.size / 4) ≤ 2^32 := by have := hInput.1; omega
  have hOutputSize : (addRows left right).size = 4 * (left.size / 4) := PackedSource.generate_size _ _
  have hParamLength : frame.params.length = 6 := by rw [hParams]; rfl
  have hCapacity : (need left).toNat = PackedCapacity.capacityNat (4 * (left.size / 4)) :=
    PackedCapacity.capacity_toNat _ hCount
  have hNeed : 4 * (left.size / 4) ≤ (need left).toNat := by
    rw [hCapacity]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (need left) hHeap hBound
  have hInputAllocated := hAllocFrame.packed hInputProtected hInput
  have hRightAllocated := hAllocFrame.packed hRightProtected hRight
  have hRightSep := hRightProtected.allocated_disjoint (need left) hBound
  have hBounds := PackedAllocation.root_bounds initial heap.top (need left) heap.nodes hHeap.freeList hBound
  have hSep := hInputProtected.allocated_disjoint (need left) hBound
  have hSpace := allocated_capacity (need left) heap.nodes
  rw [emitted_body]
  simp only [List.append_assoc]
  apply size_spec env initial frame left hParamLength hLocals hValues
    (by rw [hParams]; rfl) (by have := hInput.1; omega)
  apply PackedCapacity.program_spec 20 22 (UInt64.ofNat (4 * (left.size / 4))) «module» env initial
    (sizeFrame frame left)
  · simp [sizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [sizeFrame, hParamLength]
  · simp [sizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (sizeFrame frame left) 22 (need left)
  have hPreparedParams : prepared.params = frame.params := by simp [prepared, FixedArrayCapacity.capacityFrame, sizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 22 := by simp [prepared, FixedArrayCapacity.capacityFrame, sizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      sizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 22 heap.top
    (need left) heap.allocations heap.nodes
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
    List.getElem?_append, List.getElem?_take, show min 16 22 = 16 from rfl]
  apply loop_spec env (heap.allocatePackedStore initial (need left))
    leftOwner rightOwner leftPtr rightPtr (allocatedRoot heap.top (need left) heap.nodes) left right _
    hInputAllocated hRightAllocated hRightSize
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
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
  have hOutput := heap.packedOutput initial final (need left) (addRows left right) hHeap
    (by rw [hOutputSize]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [hOutputSize]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[15]? = some (.i64 (allocatedRoot heap.top (need left) heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  simp only [parameters] at hResultParams
  simp only [func30, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hResultParams, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · rw [hOutputSize]
  · exact hOutput

#print axioms body_spec

end Project.Gpt2CachedStep.AddRows
