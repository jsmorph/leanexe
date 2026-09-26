import Project.Gpt2CachedStep.CachedAttention.FrozenSums
import Project.Gpt2CachedStep.CachedAttention.FrozenProbabilitiesLoop
import Project.Gpt2CachedStep.CachedAttention.FrozenMatrixSize

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def ProbabilitiesBuiltState (params : List Wasm.Value) (scorePtr maximumPtr exponentialPtr sumPtr probabilityPtr : UInt64)
    (position : Nat) (frame : Locals) : Prop :=
  SumsBuiltState params scorePtr maximumPtr exponentialPtr sumPtr position frame ∧
  frame.locals[65]? = some (.i64 probabilityPtr) ∧ frame.locals[66]? = some (.i64 probabilityPtr) ∧
  frame.locals[67]? = some (.i64 (UInt64.ofNat (4 * (12 * (position + 1)))))

set_option maxRecDepth 32768 in
theorem emitted_probabilities_prefix : (func29.drop 222).take 56 = matrixSizeCode 62 ++ PackedCapacity.program 109 111 ++
    PackedAllocation.program 111 ++ [.localGet 116, .localSet 110, .constI64 0, .localSet 63] ++
    (func29.drop 271).take 1 ++
    [.localGet 110, .localSet 73, .localGet 73, .localSet 74, .localGet 62, .localSet 75] := rfl

set_option maxRecDepth 32768 in
theorem probabilities_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Wasm.Value) (scorePtr maximumPtr exponentialPtr sumPtr : UInt64) (exponentialValues sumValues : ByteArray)
    (position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hExponentials : ByteArrayAt initial.mem exponentialPtr.toNat exponentialValues)
    (hSums : ByteArrayAt initial.mem sumPtr.toNat sumValues)
    (hSumSize : sumValues.size = 48) (hPosition : position < 128)
    (hExponentialSize : exponentialValues.size = 4 * (12 * (position + 1)))
    (hExponentialProtected : heap.Protects exponentialPtr.toNat (exponentialPtr.toNat + exponentialValues.size))
    (hSumProtected : heap.Protects sumPtr.toNat (sumPtr.toNat + sumValues.size))
    (hBump : takeFirstFitFrom 0 (scoresNeed position) heap.nodes = none →
      heap.top.toNat + 48 + (scoresNeed position).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (scoresNeed position) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) (hParamsLength : params.length = 8)
    (hState : SumsBuiltState params scorePtr maximumPtr exponentialPtr sumPtr position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      ProbabilitiesBuiltState params scorePtr maximumPtr exponentialPtr sumPtr (allocatedRoot heap.top (scoresNeed position) heap.nodes) position result →
      heap.PackedOutput initial final (scoresNeed position) (probabilities exponentialValues sumValues (position + 1)) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 222).take 56 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨⟨⟨hParams, hLocals, hValues, hSize, hScoreOwner, hScorePointer, hScoreBytes, hTyped⟩,
    hMaximumOwner, hMaximumPointer, hMaximumBytes⟩, hExponentialOwner, hExponentialPointer, hExponentialBytes⟩,
    hSumOwner, hSumPointer, hSumBytes⟩
  have hParamLength : frame.params.length = 8 := by rw [hParams, hParamsLength]
  have hCount : 4 * (12 * (position + 1)) ≤ 2^32 := by omega
  have hNeed : 4 * (12 * (position + 1)) ≤ (scoresNeed position).toNat := by
    rw [scoresNeed, PackedCapacity.capacity_toNat _ hCount]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (scoresNeed position) hHeap hBound
  have hExponentialsAllocated := hAllocFrame.packed hExponentialProtected hExponentials
  have hSumsAllocated := hAllocFrame.packed hSumProtected hSums
  have hSumSep := hSumProtected.allocated_disjoint (scoresNeed position) hBound
  have hExponentialSep := hExponentialProtected.allocated_disjoint (scoresNeed position) hBound
  have hBounds := PackedAllocation.root_bounds initial heap.top (scoresNeed position) heap.nodes hHeap.freeList hBound
  have hSpace := allocated_capacity (scoresNeed position) heap.nodes
  rw [emitted_probabilities_prefix]
  simp only [List.append_assoc]
  apply matrixSize_spec env initial frame (position + 1) 62 hParamLength hLocals hValues hSize
    (by decide) (by decide) hCount
  apply PackedCapacity.program_spec 109 111 (UInt64.ofNat (4 * (12 * (position + 1)))) «module» env initial (matrixSizeFrame frame (position + 1) 62)
  · simp [matrixSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [matrixSizeFrame, hParamLength]
  · simp [matrixSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (matrixSizeFrame frame (position + 1) 62) 111 (scoresNeed position)
  have hPreparedParams : prepared.params = frame.params := by simp [prepared, FixedArrayCapacity.capacityFrame, matrixSizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 114 := by simp [prepared, FixedArrayCapacity.capacityFrame, matrixSizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      matrixSizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 111 heap.top
    (scoresNeed position) heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]; decide
  · simp [prepared, FixedArrayCapacity.capacityFrame, matrixSizeFrame, Locals.get, hParamLength, hLocals]
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
    List.getElem?_append, List.getElem?_take, show min 103 114 = 103 from rfl]
  apply probabilitiesLoop_spec env (heap.allocatePackedStore initial (scoresNeed position))
    params (frame.locals.take 54) exponentialPtr sumPtr (allocatedRoot heap.top (scoresNeed position) heap.nodes) exponentialValues sumValues position _
    hExponentialsAllocated hSumsAllocated (by rw [hExponentialSize]) (by rw [hSumSize]) hPosition
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame, matrixSizeFrame,
      Locals.get, Locals.validIndex, hParams, hParamsLength, hLocals]
    rfl
  · simp [hLocals] at hSize hExponentialOwner hExponentialPointer hExponentialBytes hSumOwner hSumPointer hSumBytes
    simp (config := { maxDischargeDepth := 64 }) [ProbabilitiesState, prepared,
      FixedArrayCapacity.capacityFrame, matrixSizeFrame, hParams, hParamsLength, hLocals,
      hSize, hExponentialOwner, hExponentialPointer, hExponentialBytes, hExponentialSize, hSumSize,
      hSumOwner, hSumPointer, hSumBytes, List.take_set_of_le, List.take_append, List.take_take,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final (scoresNeed position) (probabilities exponentialValues sumValues (position + 1)) hHeap
    (by rw [probabilities_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [probabilities_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultParamLength, hResultLocals, hResultSize,
    hResultExponentialOwner, hResultExponentialPtr, hResultExponentialBytes,
    hResultSumOwner, hResultSumPtr, hResultSumBytes, hByteLength, hResultTyped, hPrefix⟩
  have hResultPointer : result.locals[102]? = some (.i64 (allocatedRoot heap.top (scoresNeed position) heap.nodes)) := by
    simpa [Locals.get, hResultParamLength, hResultLocals] using hReady.2.2.2.1
  wp_packed_frame [hResultParams, hParamsLength, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [ProbabilitiesBuiltState, SumsBuiltState, ExponentialsBuiltState, MaximaBuiltState, ScoresBuiltState,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hResultTyped, Frame.local_of_take_eq hPrefix,
      hSize, hScoreOwner, hScorePointer, hScoreBytes, hMaximumOwner, hMaximumPointer, hMaximumBytes,
      hExponentialOwner, hExponentialPointer, hExponentialBytes, hSumOwner, hSumPointer, hSumBytes, and_self]
  · exact hOutput

#print axioms probabilities_spec

end Project.Gpt2CachedStep.Frozen.CachedAttention
