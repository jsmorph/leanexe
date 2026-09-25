import Project.LebU32.Frames

namespace Project.LebU32.Spec
open Wasm Project.ProofKit Project.EulerRiemann.Execution PackedFloatFrame

theorem continuePush_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (frame : Locals) (fuel value source : UInt64) (bytes : ByteArray)
    (hFrame : BranchFrame frame fuel value source (UInt64.ofNat bytes.size))
    (hHeap : heap.At initial) (hBytes : PackedMemory.ByteArrayAt initial.mem source.toNat bytes)
    (hProtected : heap.Protects source.toNat (source.toNat + bytes.size))
    (hSize : bytes.size + 1 ≤ 4294967296)
    (hBump : Project.Runtime.takeFirstFitFrom 0 (PackedPush.need bytes) heap.nodes = none →
      heap.top.toNat + 48 + (PackedPush.need bytes).toNat < 4294967296 ∧
      FixedArrayBump.requiredPages heap.top (PackedPush.need bytes) ≤ initial.memoryCap «module» 0)
    (hPages : initial.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      AdvanceFrame result fuel value source (UInt64.ofNat bytes.size)
        (allocatedRoot heap.top (PackedPush.need bytes) heap.nodes) →
      heap.PackedOutput initial final (PackedPush.need bytes) (bytes.push (value % 128 + 128).toUInt8) →
      final.mem.pages = (heap.allocatePackedStore initial (PackedPush.need bytes)).mem.pages →
      wp «module» rest Q final result env) :
    wp «module» (continueByteCode.take 69 ++ rest) Q initial frame env := by
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  have hLow := hFrame.low
  have hQuotient := hFrame.quotient
  let prepared : Locals :=
    { params := [.i64 fuel, .i64 value, .i64 source, .i64 source, .i64 (UInt64.ofNat bytes.size)]
      locals := ((((((frame.locals.set 11 (.i64 (value / 128))).set 12
        (.i64 (value % 128 + 128 &&& 255))).set 13 (.i64 source)).set 14
        (.i64 (UInt64.ofNat bytes.size))).set 24 (.i64 source)).set 25
        (.i64 (UInt64.ofNat bytes.size))).set 26 (.i64 (value % 128 + 128 &&& 255))
      values := [] }
  have hPreparedLocals : prepared.locals.length = 36 := by simp [prepared, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    exact ((((((hFrame.typed.set _ _).set _ _).set _ _).set _ _).set _ _).set _ _).set _ _
  have hShape : continueByteCode.take 69 =
      [.localGet 11, .localSet 16, .localGet 10, .constI64 128, .addI64,
       .constI64 255, .andI64, .localSet 17, .localGet 3, .localSet 18,
       .localGet 4, .localSet 19, .localGet 18, .localSet 29, .localGet 19, .localSet 30,
       .localGet 17, .localSet 31] ++ PackedPush.program 29 ++
      [.localSet 21, .localGet 21, .localSet 22, .localGet 19, .constI64 1, .addI64, .localSet 23] := rfl
  rw [hShape, List.append_assoc, List.append_assoc]
  wp_packed_frame [hParams, hLocals, hValues, hLow, hQuotient]
  change wp «module» (PackedPush.program 29 ++ _) Q initial prepared env
  apply PackedPush.program_spec 29 «module» env initial heap prepared source (value % 128 + 128 &&& 255) bytes
    hHeap hBytes hProtected hSize hBump hPages rfl (by change 5 ≤ 29; decide)
    (by simp [prepared, hLocals]) rfl hPreparedTyped
    (by simp [prepared, Locals.get, hLocals])
    (by simp [prepared, Locals.get, hLocals])
    (by simp [prepared, Locals.get, hLocals])
  intro final result hStack hPreserved hOutput hFinalPages
  have hResultParams : result.params = prepared.params := hPreserved.1
  have hResultLocals : result.locals.length = 36 := hPreserved.2.1.trans hPreparedLocals
  have hRead (index : Nat) (hi : index < 24) : result.locals[index]? = prepared.locals[index]? := by
    have hGet := hPreserved.2.2.2 (index + 5) (Or.inl (by omega))
    simpa [Locals.get, hResultParams, prepared, hResultLocals, hLocals,
      show index < 36 by omega, show index + 5 < 41 by omega] using hGet
  have hLengthLocal : result.locals[14]? = some (.i64 (UInt64.ofNat bytes.size)) := by
    rw [hRead 14 (by decide)]
    simp [prepared, hLocals]
  have hTracker : result.locals[0]? = some (.i64 source) := by
    rw [hRead 0 (by decide)]
    simpa [prepared, hLocals] using hFrame.tracker
  have hDone : result.locals[4]? = some (.i64 0) := by
    rw [hRead 4 (by decide)]
    simpa [prepared, hLocals] using hFrame.done
  have hQuotientLocal : result.locals[11]? = some (.i64 (value / 128)) := by
    rw [hRead 11 (by decide)]
    simp [prepared, hLocals]
  have hTrackerValue := (List.getElem_of_getElem? hTracker).2
  have hDoneValue := (List.getElem_of_getElem? hDone).2
  have hQuotientValue := (List.getElem_of_getElem? hQuotientLocal).2
  wp_packed_frame [hResultParams, prepared, hResultLocals, hStack, hLengthLocal]
  apply hNext
  · refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hResultLocals]
    · exact ((hPreserved.2.2.1.set _ _).set _ _).set _ _
    all_goals simp [hResultLocals, hTrackerValue, hDoneValue, hQuotientValue]
  · simpa only [masked_byte] using hOutput
  · exact hFinalPages

#print axioms continuePush_spec
end Project.LebU32.Spec
