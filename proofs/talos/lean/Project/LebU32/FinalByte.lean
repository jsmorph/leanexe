import Project.LebU32.Frames

namespace Project.LebU32.Spec
open Wasm Project.ProofKit Project.EulerRiemann.Execution PackedFloatFrame

theorem finalByte_spec (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
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
      FinishedFrame result fuel (allocatedRoot heap.top (PackedPush.need bytes) heap.nodes)
        (UInt64.ofNat (bytes.size + 1)) →
      heap.PackedOutput initial final (PackedPush.need bytes) (bytes.push (value % 128).toUInt8) →
      final.mem.pages = (heap.allocatePackedStore initial (PackedPush.need bytes)).mem.pages →
      wp «module» rest Q final result env) :
    wp «module» (finalByteCode ++ rest) Q initial frame env := by
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  have hLow := hFrame.low
  let prepared : Locals :=
    { params := [.i64 fuel, .i64 value, .i64 source, .i64 source, .i64 (UInt64.ofNat bytes.size)]
      locals := (((((frame.locals.set 7 (.i64 (value % 128 &&& 255))).set 8 (.i64 source)).set 9
        (.i64 (UInt64.ofNat bytes.size))).set 24 (.i64 source)).set 25
        (.i64 (UInt64.ofNat bytes.size))).set 26 (.i64 (value % 128 &&& 255))
      values := [] }
  have hPreparedLocals : prepared.locals.length = 36 := by simp [prepared, hLocals]
  have hPreparedTyped : I64Values prepared.locals := by
    exact (((((hFrame.typed.set _ _).set _ _).set _ _).set _ _).set _ _).set _ _
  have hPrefix : finalByteCode.take 14 =
      [.localGet 10, .constI64 255, .andI64, .localSet 12, .localGet 3, .localSet 13,
       .localGet 4, .localSet 14, .localGet 13, .localSet 29, .localGet 14, .localSet 30,
       .localGet 12, .localSet 31] := rfl
  rw [final_push_shape, List.append_assoc, List.append_assoc, hPrefix]
  wp_packed_frame [hParams, hLocals, hValues, hLow]
  change wp «module» (PackedPush.program 29 ++ _) Q initial prepared env
  apply PackedPush.program_spec 29 «module» env initial heap prepared source (value % 128 &&& 255) bytes
    hHeap hBytes hProtected hSize hBump hPages rfl (by change 5 ≤ 29; decide)
    (by simp [prepared, hLocals]) rfl hPreparedTyped
    (by simp [prepared, Locals.get, hLocals])
    (by simp [prepared, Locals.get, hLocals])
    (by simp [prepared, Locals.get, hLocals])
  intro final result hStack hPreserved hOutput hFinalPages
  have hResultParams : result.params = prepared.params := hPreserved.1
  have hResultLocals : result.locals.length = 36 := hPreserved.2.1.trans hPreparedLocals
  have hLengthRead : result.get 14 = some (.i64 (UInt64.ofNat bytes.size)) := by
    rw [hPreserved.2.2.2 14 (Or.inl (by decide))]
    simp [prepared, Locals.get, hLocals]
  have hLengthLocal : result.locals[9]? = some (.i64 (UInt64.ofNat bytes.size)) := by
    simpa [Locals.get, hResultParams, prepared, hResultLocals] using hLengthRead
  have hSuffix : finalByteCode.drop 58 =
      [.localSet 15, .localGet 15, .localSet 6, .localGet 15, .localSet 7,
       .localGet 14, .constI64 1, .addI64, .localSet 8, .constI64 1, .localSet 9] := rfl
  rw [hSuffix]
  wp_packed_frame [hResultParams, prepared, hResultLocals, hStack, hLengthLocal,
    ← UInt64.ofNat_add]
  apply hNext
  · refine ⟨rfl, rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · simp [hResultLocals]
    · exact ((((hPreserved.2.2.1.set _ _).set _ _).set _ _).set _ _).set _ _
    all_goals simp [hResultLocals]
  · simpa only [masked_byte] using hOutput
  · exact hFinalPages

#print axioms finalByte_spec
end Project.LebU32.Spec
