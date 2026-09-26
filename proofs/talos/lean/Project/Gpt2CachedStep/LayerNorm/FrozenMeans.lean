import Project.Gpt2CachedStep.LayerNorm.FrozenSize
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2CachedStep.Frozen.LayerNorm
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def temporaryNeed (rows : Nat) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (4 * rows))

def MeansBuiltState (params : List Wasm.Value) (pointer : UInt64) (rows : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 74 ∧ frame.values = [] ∧
  frame.locals[7]? = some (.i64 pointer) ∧ frame.locals[8]? = some (.i64 pointer) ∧
  frame.locals[9]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧ I64Values frame.locals

set_option maxRecDepth 32768 in
theorem emitted_means_prefix : func20.take 49 = sizeCode 9 ++ PackedCapacity.program 70 72 ++
    PackedAllocation.program 72 ++ [.localGet 77, .localSet 71, .constI64 0, .localSet 10] ++
    (func20.drop 42).take 1 ++
    [.localGet 71, .localSet 16, .localGet 16, .localSet 17, .localGet 9, .localSet 18] := rfl

set_option maxRecDepth 32768 in
theorem means_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (weightsOwner inputOwner weightsPtr inputPtr : UInt64) (weights input : ByteArray)
    (scaleOffset biasOffset rows : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hInputSize : rows * 768 * 4 ≤ input.size)
    (hInputProtected : heap.Protects inputPtr.toNat (inputPtr.toNat + input.size))
    (hCount : 4 * rows ≤ 2^32)
    (hBump : takeFirstFitFrom 0 (temporaryNeed rows) heap.nodes = none →
      heap.top.toNat + 48 + (temporaryNeed rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (temporaryNeed rows) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters weightsOwner inputOwner weightsPtr inputPtr weights input scaleOffset biasOffset rows)
    (hLocals : frame.locals.length = 74) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      MeansBuiltState (parameters weightsOwner inputOwner weightsPtr inputPtr weights input scaleOffset biasOffset rows)
        (allocatedRoot heap.top (temporaryNeed rows) heap.nodes) rows result →
      heap.PackedOutput initial final (temporaryNeed rows) (means input rows) →
      wp «module» rest Q final result env) :
    wp «module» (func20.take 49 ++ rest) Q initial frame env := by
  have hParamLength : frame.params.length = 9 := by rw [hParams]; rfl
  have hCapacity : (temporaryNeed rows).toNat = PackedCapacity.capacityNat (4 * rows) :=
    PackedCapacity.capacity_toNat _ hCount
  have hNeed : 4 * rows ≤ (temporaryNeed rows).toNat := by
    rw [hCapacity]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (temporaryNeed rows) hHeap hBound
  have hInputAllocated := hAllocFrame.packed hInputProtected hInput
  have hBounds := PackedAllocation.root_bounds initial heap.top (temporaryNeed rows) heap.nodes hHeap.freeList hBound
  have hSep := hInputProtected.allocated_disjoint (temporaryNeed rows) hBound
  have hSpace := allocated_capacity (temporaryNeed rows) heap.nodes
  rw [emitted_means_prefix]
  simp only [List.append_assoc]
  apply sizeCode_spec env initial frame 9 rows hParamLength hLocals hValues
    (by rw [hParams]; rfl) (by decide) (by decide) hCount
  apply PackedCapacity.program_spec 70 72 (UInt64.ofNat (4 * rows)) «module» env initial
    (sizeFrame frame 9 rows)
  · simp [sizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [sizeFrame, hParamLength]
  · simp [sizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (sizeFrame frame 9 rows) 72 (temporaryNeed rows)
  have hPreparedParams : prepared.params = frame.params := by simp [prepared, FixedArrayCapacity.capacityFrame, sizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 74 := by simp [prepared, FixedArrayCapacity.capacityFrame, sizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      sizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 72 heap.top
    (temporaryNeed rows) heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]; decide
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
    List.getElem?_append, List.getElem?_take, show min 63 74 = 63 from rfl]
  apply meansLoop_spec env (heap.allocatePackedStore initial (temporaryNeed rows))
    weightsOwner inputOwner weightsPtr inputPtr (allocatedRoot heap.top (temporaryNeed rows) heap.nodes)
    weights input scaleOffset biasOffset rows _ hInputAllocated hInputSize
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · simp [PackedGenerateLoop.Ready,
      prepared, FixedArrayCapacity.capacityFrame, sizeFrame, Locals.get, Locals.validIndex,
      hParams, parameters, hLocals]
    rfl
  · simp (config := { maxDischargeDepth := 64 }) [MeansState,
      prepared,
      FixedArrayCapacity.capacityFrame, sizeFrame, hParams, parameters, hLocals,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final (temporaryNeed rows) (means input rows) hHeap
    (by rw [means_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [means_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[62]? = some (.i64 (allocatedRoot heap.top (temporaryNeed rows) heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  simp only [parameters] at hResultParams
  wp_packed_frame [hResultParams, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [MeansBuiltState, parameters,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hResultTyped, and_self]
  · exact hOutput

#print axioms means_spec

end Project.Gpt2CachedStep.Frozen.LayerNorm
