import Project.Gpt2CachedStep.CachedAttention.Maxima
import Project.Gpt2CachedStep.CachedAttention.ExponentialsLoop
import Project.Gpt2CachedStep.CachedAttention.MatrixSize

namespace Project.Gpt2CachedStep.CachedAttention
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def ExponentialsBuiltState (params : List Wasm.Value) (scorePtr maximumPtr exponentialPtr : UInt64)
    (position : Nat) (frame : Locals) : Prop :=
  MaximaBuiltState params scorePtr maximumPtr position frame ∧
  frame.locals[40]? = some (.i64 exponentialPtr) ∧ frame.locals[41]? = some (.i64 exponentialPtr) ∧
  frame.locals[42]? = some (.i64 (UInt64.ofNat (4 * (12 * (position + 1)))))

set_option maxRecDepth 32768 in
theorem emitted_exponentials_prefix : (func29.drop 117).take 56 = matrixSizeCode 36 ++ PackedCapacity.program 109 111 ++
    PackedAllocation.program 111 ++ [.localGet 116, .localSet 110, .constI64 0, .localSet 37] ++
    (func29.drop 166).take 1 ++
    [.localGet 110, .localSet 48, .localGet 48, .localSet 49, .localGet 36, .localSet 50] := rfl

set_option maxRecDepth 32768 in
theorem exponentials_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Wasm.Value) (scorePtr maximumPtr : UInt64) (scoreValues maximumValues : ByteArray)
    (position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hScores : ByteArrayAt initial.mem scorePtr.toNat scoreValues)
    (hMaxima : ByteArrayAt initial.mem maximumPtr.toNat maximumValues)
    (hMaximumSize : maximumValues.size = 48) (hPosition : position < 128)
    (hScoreSize : scoreValues.size = 4 * (12 * (position + 1)))
    (hScoreProtected : heap.Protects scorePtr.toNat (scorePtr.toNat + scoreValues.size))
    (hMaximumProtected : heap.Protects maximumPtr.toNat (maximumPtr.toNat + maximumValues.size))
    (hBump : takeFirstFitFrom 0 (scoresNeed position) heap.nodes = none →
      heap.top.toNat + 48 + (scoresNeed position).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (scoresNeed position) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) (hParamsLength : params.length = 8)
    (hState : MaximaBuiltState params scorePtr maximumPtr position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      ExponentialsBuiltState params scorePtr maximumPtr (allocatedRoot heap.top (scoresNeed position) heap.nodes) position result →
      heap.PackedOutput initial final (scoresNeed position) (exponentials scoreValues maximumValues (position + 1)) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 117).take 56 ++ rest) Q initial frame env := by
  rcases hState with ⟨⟨hParams, hLocals, hValues, hSize, hScoreOwner, hScorePointer, hScoreBytes, hTyped⟩,
    hMaximumOwner, hMaximumPointer, hMaximumBytes⟩
  have hParamLength : frame.params.length = 8 := by rw [hParams, hParamsLength]
  have hCount : 4 * (12 * (position + 1)) ≤ 2^32 := by omega
  have hNeed : 4 * (12 * (position + 1)) ≤ (scoresNeed position).toNat := by
    rw [scoresNeed, PackedCapacity.capacity_toNat _ hCount]
    exact PackedCapacity.capacityNat_ge _
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial (scoresNeed position) hHeap hBound
  have hScoresAllocated := hAllocFrame.packed hScoreProtected hScores
  have hMaximaAllocated := hAllocFrame.packed hMaximumProtected hMaxima
  have hMaximumSep := hMaximumProtected.allocated_disjoint (scoresNeed position) hBound
  have hScoreSep := hScoreProtected.allocated_disjoint (scoresNeed position) hBound
  have hBounds := PackedAllocation.root_bounds initial heap.top (scoresNeed position) heap.nodes hHeap.freeList hBound
  have hSpace := allocated_capacity (scoresNeed position) heap.nodes
  rw [emitted_exponentials_prefix]
  simp only [List.append_assoc]
  apply matrixSize_spec env initial frame (position + 1) 36 hParamLength hLocals hValues hSize
    (by decide) (by decide) hCount
  apply PackedCapacity.program_spec 109 111 (UInt64.ofNat (4 * (12 * (position + 1)))) «module» env initial (matrixSizeFrame frame (position + 1) 36)
  · simp [matrixSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [matrixSizeFrame, hParamLength]
  · simp [matrixSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (matrixSizeFrame frame (position + 1) 36) 111 (scoresNeed position)
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
  apply exponentialsLoop_spec env (heap.allocatePackedStore initial (scoresNeed position))
    params scorePtr maximumPtr (allocatedRoot heap.top (scoresNeed position) heap.nodes) scoreValues maximumValues position _
    hScoresAllocated hMaximaAllocated (by rw [hScoreSize]) (by rw [hMaximumSize]) hPosition
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame, matrixSizeFrame,
      Locals.get, Locals.validIndex, hParams, hParamsLength, hLocals]
    rfl
  · simp [hLocals] at hSize hScoreOwner hScorePointer hScoreBytes hMaximumOwner hMaximumPointer hMaximumBytes
    simp (config := { maxDischargeDepth := 64 }) [ExponentialsState, prepared,
      FixedArrayCapacity.capacityFrame, matrixSizeFrame, hParams, hParamsLength, hLocals,
      hSize, hScoreOwner, hScorePointer, hScoreBytes, hScoreSize, hMaximumSize,
      hMaximumOwner, hMaximumPointer, hMaximumBytes,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final (scoresNeed position) (exponentials scoreValues maximumValues (position + 1)) hHeap
    (by rw [exponentials_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [exponentials_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultParamLength, hResultLocals, hResultSize,
    hResultScoreOwner, hResultScorePtr, hResultScoreBytes,
    hResultMaximumOwner, hResultMaximumPtr, hResultMaximumBytes, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[102]? = some (.i64 (allocatedRoot heap.top (scoresNeed position) heap.nodes)) := by
    simpa [Locals.get, hResultParamLength, hResultLocals] using hReady.2.2.2.1
  wp_packed_frame [hResultParams, hParamsLength, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [ExponentialsBuiltState, MaximaBuiltState, ScoresBuiltState,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hResultTyped, hResultSize, hResultScoreOwner, hResultScorePtr,
      hResultScoreBytes, hScoreSize, hMaximumSize,
      hResultMaximumOwner, hResultMaximumPtr, hResultMaximumBytes,
      show UInt64.ofNat 48 = 48 from rfl, and_self]
  · exact hOutput

#print axioms exponentials_spec

end Project.Gpt2CachedStep.CachedAttention
