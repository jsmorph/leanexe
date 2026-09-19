import Project.Gpt2CachedStep.CachedAttention.Scores
import Project.Gpt2CachedStep.CachedAttention.MaximaLoop
import Project.Gpt2CachedStep.CachedAttention.FixedSize

namespace Project.Gpt2CachedStep.CachedAttention
open Wasm Project.Runtime Project.ProofKit PackedMemory PackedFloatFrame Project.EulerRiemann.Execution

def maximaNeed : UInt64 := PackedCapacity.capacity 48

def MaximaBuiltState (params : List Wasm.Value) (scorePtr maximumPtr : UInt64)
    (position : Nat) (frame : Locals) : Prop :=
  ScoresBuiltState params scorePtr position frame ∧
  frame.locals[25]? = some (.i64 maximumPtr) ∧ frame.locals[26]? = some (.i64 maximumPtr) ∧
  frame.locals[27]? = some (.i64 48)

set_option maxRecDepth 32768 in
theorem emitted_maxima_prefix : (func29.drop 68).take 49 = fixedSizeCode 12 25 ++ PackedCapacity.program 109 111 ++
    PackedAllocation.program 111 ++ [.localGet 116, .localSet 110, .constI64 0, .localSet 26] ++
    (func29.drop 110).take 1 ++
    [.localGet 110, .localSet 33, .localGet 33, .localSet 34, .localGet 25, .localSet 35] := rfl

set_option maxRecDepth 32768 in
theorem maxima_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params : List Wasm.Value) (scorePtr : UInt64) (scoreValues : ByteArray)
    (position : Nat) (frame : Locals)
    (hHeap : heap.At initial)
    (hScores : ByteArrayAt initial.mem scorePtr.toNat scoreValues)
    (hScoreSize : scoreValues.size = 4 * (12 * (position + 1)))
    (hScoreProtected : heap.Protects scorePtr.toNat (scorePtr.toNat + scoreValues.size))
    (hBump : takeFirstFitFrom 0 maximaNeed heap.nodes = none →
      heap.top.toNat + 48 + maximaNeed.toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top maximaNeed ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) (hParamsLength : params.length = 8)
    (hState : ScoresBuiltState params scorePtr position frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      MaximaBuiltState params scorePtr (allocatedRoot heap.top maximaNeed heap.nodes) position result →
      heap.PackedOutput initial final maximaNeed (maxima scoreValues (position + 1)) →
      wp «module» rest Q final result env) :
    wp «module» ((func29.drop 68).take 49 ++ rest) Q initial frame env := by
  rcases hState with ⟨hParams, hLocals, hValues, hSize, hScoreOwner, hScorePointer, hScoreBytes, hTyped⟩
  have hParamLength : frame.params.length = 8 := by rw [hParams, hParamsLength]
  have hNeed : 48 ≤ maximaNeed.toNat := by decide
  have hBound := fun h => (hBump h).1.le
  have hAllocFrame := heap.frame_allocatePacked initial maximaNeed hHeap hBound
  have hScoresAllocated := hAllocFrame.packed hScoreProtected hScores
  have hScoreSep := hScoreProtected.allocated_disjoint maximaNeed hBound
  have hBounds := PackedAllocation.root_bounds initial heap.top maximaNeed heap.nodes hHeap.freeList hBound
  have hSpace := allocated_capacity maximaNeed heap.nodes
  rw [emitted_maxima_prefix]
  simp only [List.append_assoc]
  apply fixedSize_spec env initial frame 12 25 hParamLength hLocals hValues
    (by decide) (by decide) (by decide)
  apply PackedCapacity.program_spec 109 111 48 «module» env initial (fixedSizeFrame frame 12 25)
  · simp [fixedSizeFrame, Locals.get, hParamLength, hLocals]
  · rfl
  · simp [fixedSizeFrame, hParamLength]
  · simp [fixedSizeFrame, Locals.validIndex, hParamLength, hLocals]
  let prepared := FixedArrayCapacity.capacityFrame (fixedSizeFrame frame 12 25) 111 maximaNeed
  have hPreparedParams : prepared.params = frame.params := by simp [prepared, FixedArrayCapacity.capacityFrame, fixedSizeFrame, hParamLength]
  have hPreparedLocals : prepared.locals.length = 114 := by simp [prepared, FixedArrayCapacity.capacityFrame, fixedSizeFrame, hParamLength, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    simp (config := { maxDischargeDepth := 64 }) only [prepared, FixedArrayCapacity.capacityFrame,
      fixedSizeFrame, hParamLength, Nat.reduceSub, I64Values.set, hTyped]
  apply PackedAllocation.program_spec_frame «module» env initial prepared 111 heap.top
    maximaNeed heap.allocations heap.nodes
  · rfl
  · exact hPreparedTyped
  · rw [hPreparedParams, hParamLength]; decide
  · rw [hPreparedParams, hParamLength, hPreparedLocals]; decide
  · simp [prepared, FixedArrayCapacity.capacityFrame, fixedSizeFrame, Locals.get, hParamLength, hLocals]
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
  apply maximaLoop_spec env (heap.allocatePackedStore initial maximaNeed)
    params scorePtr (allocatedRoot heap.top maximaNeed heap.nodes) scoreValues position _ hScoresAllocated
  · rw [hScoreSize]; omega
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.1
  · exact (Nat.add_le_add_left hNeed _).trans hBounds.2
  · omega
  · simp [PackedGenerateLoop.Ready, prepared, FixedArrayCapacity.capacityFrame, fixedSizeFrame,
      Locals.get, Locals.validIndex, hParams, hParamsLength, hLocals]
    rfl
  · simp [hLocals] at hSize hScoreOwner hScorePointer hScoreBytes
    simp (config := { maxDischargeDepth := 64 }) [MaximaState, prepared,
      FixedArrayCapacity.capacityFrame, fixedSizeFrame, hParams, hParamsLength, hLocals,
      hSize, hScoreOwner, hScorePointer, hScoreBytes, hScoreSize,
      I64Values.set, I64Values.append, I64Values.cons, I64Values.take, I64Values.drop, hTyped]
  intro final result hReady hState hBytes hWrites
  have hOutput := heap.packedOutput initial final maximaNeed (maxima scoreValues (position + 1)) hHeap
    (by rw [maxima_size]; exact hNeed) (fun h => (hBump h).1) hPages
    (by rw [maxima_size]; exact hWrites) hBytes
  rcases hState with ⟨hResultParams, hResultParamLength, hResultLocals, hResultSize,
    hResultScoreOwner, hResultScorePtr, hResultScoreBytes, hByteLength, hResultTyped⟩
  have hResultPointer : result.locals[102]? = some (.i64 (allocatedRoot heap.top maximaNeed heap.nodes)) := by
    simpa [Locals.get, hResultParamLength, hResultLocals] using hReady.2.2.2.1
  wp_packed_frame [hResultParams, hParamsLength, hResultLocals, hReady.1, hResultPointer, hByteLength]
  apply hNext
  · simp (config := { maxDischargeDepth := 64 }) only [MaximaBuiltState, ScoresBuiltState,
      hResultLocals, List.length_set, List.getElem?_set, Nat.reduceEqDiff, Nat.reduceLT, reduceIte,
      I64Values.set, hResultTyped, hResultSize, hResultScoreOwner, hResultScorePtr,
      hResultScoreBytes, hScoreSize, and_self]
  · exact hOutput

#print axioms maxima_spec

end Project.Gpt2CachedStep.CachedAttention
