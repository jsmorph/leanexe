import Project.Gpt2QuantizedCached.Embedding.Loop
import Project.Gpt2QuantizedCached.Embedding.Scale
import Project.Gpt2QuantizedCached.Embedding.Size
import Project.ProofKit.PackedCapacity
import Project.ProofKit.PackedAllocationFrame
import Project.ProofKit.OwnedPacked

namespace Project.Gpt2QuantizedCached.Embedding
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution
open LeanExe.Models.Gpt2.Quantized

def need : UInt64 := PackedCapacity.capacity 3072

theorem output_size (weights : ByteArray) (token : UInt32) (position : Nat) :
    (embedding weights token position).size = 3072 := by
  rw [source_eq]
  exact PackedSource.generate_size _ _

set_option maxRecDepth 32768 in
theorem emitted_body : func30 = func30.take 28 ++ (func30.drop 28).take 11 ++
    PackedCapacity.program 12 14 ++ PackedAllocation.program 14 ++
    [.localGet 19, .localSet 13, .constI64 0, .localSet 7] ++
    (func30.drop 70).take 1 ++ func30.drop 71 := rfl

set_option maxRecDepth 32768 in
theorem body_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (owner ptr : UInt64) (weights : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hHeap : heap.At initial) (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hScaleSize : tokenScaleOffset + token.toNat * 4 + 4 ≤ weights.size)
    (hTokenSize : tokenWeightOffset + token.toNat * 768 + 768 ≤ weights.size)
    (hPositionSize : positionOffset + (position * 768 + 768) * 4 ≤ weights.size)
    (hToken : token.toNat < 50257) (hPosition : position < 128)
    (hWeightsProtected : heap.Protects ptr.toNat (ptr.toNat + weights.size))
    (hBump : takeFirstFitFrom 0 need heap.nodes = none →
      heap.top.toNat + 48 + need.toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top need ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536)
    (hParams : frame.params = parameters owner ptr weights token position)
    (hLocals : frame.locals.length = 22) (hValues : frame.values = []) (hTyped : I64Values frame.locals)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      result.values = [.i64 (UInt64.ofNat (embedding weights token position).size),
        .i64 (allocatedRoot heap.top need heap.nodes),
        .i64 (allocatedRoot heap.top need heap.nodes)] →
      heap.PackedOutput initial final need (embedding weights token position) →
      wp «module» rest Q final result env) :
    wp «module» (func30 ++ rest) Q initial frame env := by
  have hParamLength : frame.params.length = 5 := by rw [hParams]; rfl
  have hNeed : 3072 ≤ need.toNat := by decide
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial need hHeap hBound
  have hWeightsAllocated := hAllocFrame.packed hWeightsProtected hWeights
  have hBounds := PackedAllocation.root_bounds initial heap.top need heap.nodes hHeap.freeList hBound
  have hSep := hWeightsProtected.allocated_disjoint need hBound
  have hSpace := allocated_capacity need heap.nodes
  rw [emitted_body]
  simp only [List.append_assoc]
  apply scale_spec env initial owner ptr weights token position frame hWeights hScaleSize hToken
    hParams hLocals hValues
  apply size_spec env initial (scaleFrame frame ptr weights token)
    (by simpa [scaleFrame] using hParamLength)
    (by simpa [scaleFrame] using hLocals) rfl
  apply PackedCapacity.program_spec 12 14 3072 «module» env initial
    (sizeFrame (scaleFrame frame ptr weights token))
  · simp [scaleFrame, sizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [scaleFrame, sizeFrame, hParamLength]
  · simp [scaleFrame, sizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (sizeFrame (scaleFrame frame ptr weights token)) 14 need
  have hPreparedParams : prepared.params = frame.params := by simp [prepared, FixedArrayCapacity.capacityFrame, scaleFrame, sizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 22 := by simp [prepared, FixedArrayCapacity.capacityFrame, scaleFrame, sizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      scaleFrame, sizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 14 heap.top
    need heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]; decide
  · simp [prepared, FixedArrayCapacity.capacityFrame, scaleFrame, sizeFrame, Locals.get, hParamLength, hLocals]
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
    List.getElem?_append, List.getElem?_take, show min 9 22 = 9 from rfl]
  apply loop_spec env (heap.allocatePackedStore initial need)
    owner ptr (allocatedRoot heap.top need heap.nodes) weights token position _
    hWeightsAllocated hTokenSize hPositionSize hToken hPosition
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame,
      scaleFrame, sizeFrame, Locals.get, Locals.validIndex, hParams, parameters, hLocals]
    rfl
  · simp (config := { maxDischargeDepth := 64 }) [State, prepared,
      FixedArrayCapacity.capacityFrame, scaleFrame, sizeFrame, hParams, parameters, hLocals,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final need (embedding weights token position) hHeap
    (by rw [output_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [output_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultLocals, hScale, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[8]? = some (.i64 (allocatedRoot heap.top need heap.nodes)) := by
    simpa [Locals.get, hResultParams, parameters, hResultLocals] using hReady.2.2.2.1
  simp only [parameters] at hResultParams
  simp only [func30, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame [hResultParams, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · rw [output_size]
    rfl
  · exact hOutput

#print axioms body_spec

end Project.Gpt2QuantizedCached.Embedding
