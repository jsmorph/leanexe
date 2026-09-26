import Project.Gpt2QuantizedLinearRows.ScaleSize
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2QuantizedLinearRows.QuantizeRows
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def scaleNeed (rows : Nat) : UInt64 := PackedCapacity.capacity (UInt64.ofNat (4 * rows))

def ScaleBuiltState (params : List Wasm.Value) (pointer : UInt64) (rows : Nat) (frame : Locals) : Prop :=
  frame.params = params ∧ frame.locals.length = 43 ∧ frame.values = [] ∧
  frame.locals[8]? = some (.i64 pointer) ∧ frame.locals[9]? = some (.i64 pointer) ∧
  frame.locals[10]? = some (.i64 (UInt64.ofNat (4 * rows))) ∧ I64Values frame.locals

theorem emitted_scales_prefix : func3.take 49 = scaleSizeCode ++ PackedCapacity.program 40 42 ++
    PackedAllocation.program 42 ++ [.localGet 47, .localSet 41, .constI64 0, .localSet 6] ++
    (func3.drop 42).take 1 ++
    [.localGet 41, .localSet 13, .localGet 13, .localSet 14, .localGet 5, .localSet 15] := rfl

set_option maxRecDepth 32768 in
theorem scales_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner ptr : UInt64) (input : ByteArray) (width rows : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hInput : ByteArrayAt initial.mem ptr.toNat input)
    (hInputSize : rows * width * 4 ≤ input.size)
    (hInputProtected : heap.Protects ptr.toNat (ptr.toNat + input.size))
    (hCount : 4 * rows ≤ 2^32)
    (hBump : takeFirstFitFrom 0 (scaleNeed rows) heap.nodes = none →
      heap.top.toNat + 48 + (scaleNeed rows).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (scaleNeed rows) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters owner ptr input width rows)
    (hLocals : frame.locals.length = 43) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      ScaleBuiltState (parameters owner ptr input width rows)
        (allocatedRoot heap.top (scaleNeed rows) heap.nodes) rows result →
      heap.PackedOutput initial final (scaleNeed rows) (quantizeRows input width rows).scales →
      wp «module» rest Q final result env) :
    wp «module» (func3.take 49 ++ rest) Q initial frame env := by
  have hParamLength : frame.params.length = 5 := by rw [hParams]; rfl
  have hCapacity : (scaleNeed rows).toNat = PackedCapacity.capacityNat (4 * rows) :=
    PackedCapacity.capacity_toNat _ hCount
  have hNeed : 4 * rows ≤ (scaleNeed rows).toNat := by
    rw [hCapacity]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (scaleNeed rows) hHeap hBound
  have hInputAllocated := hAllocFrame.packed hInputProtected hInput
  have hBounds := PackedAllocation.root_bounds initial heap.top (scaleNeed rows) heap.nodes hHeap.freeList hBound
  have hSep := hInputProtected.allocated_disjoint (scaleNeed rows) hBound
  have hSpace := allocated_capacity (scaleNeed rows) heap.nodes
  rw [emitted_scales_prefix]
  simp only [List.append_assoc]
  apply scaleSizeCode_spec env initial frame rows hParamLength hLocals hValues
    (by rw [hParams]; rfl) hCount
  apply PackedCapacity.program_spec 40 42 (UInt64.ofNat (4 * rows)) «module» env initial
    (scaleSizeFrame frame rows)
  · simp [scaleSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [scaleSizeFrame, hParamLength]
  · simp [scaleSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (scaleSizeFrame frame rows) 42 (scaleNeed rows)
  have hPreparedParams : prepared.params = frame.params := by
    simp [prepared, FixedArrayCapacity.capacityFrame, scaleSizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 43 := by
    simp [prepared, FixedArrayCapacity.capacityFrame, scaleSizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      scaleSizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 42 heap.top
    (scaleNeed rows) heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · simp [hPreparedParams, hParamLength, hPreparedLocals]
  · simp [prepared, FixedArrayCapacity.capacityFrame, scaleSizeFrame, Locals.get, hParamLength, hLocals]
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
    List.getElem?_append, List.getElem?_take, show min 37 43 = 37 from rfl]
  apply scaleLoop_spec env (heap.allocatePackedStore initial (scaleNeed rows)) owner ptr
    (allocatedRoot heap.top (scaleNeed rows) heap.nodes) input width rows _ hInputAllocated hInputSize
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame, scaleSizeFrame,
      Locals.get, Locals.validIndex, hParams, parameters, hLocals]
    rfl
  · simp (config := { maxDischargeDepth := 64 }) [ScaleState, prepared,
      FixedArrayCapacity.capacityFrame, scaleSizeFrame, hParams, parameters, hLocals,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final (scaleNeed rows) (quantizeRows input width rows).scales hHeap
    (by rw [quantized_scales_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [quantized_scales_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[36]? = some (.i64 (allocatedRoot heap.top (scaleNeed rows) heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  simp only [parameters] at hResultParams
  wp_packed_frame [hResultParams, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [ScaleBuiltState, parameters,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hResultTyped, and_self]
  · exact hOutput

#print axioms scales_spec

end Project.Gpt2QuantizedLinearRows.QuantizeRows
