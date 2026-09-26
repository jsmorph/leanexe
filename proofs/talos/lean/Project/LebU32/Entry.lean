import Project.LebU32.Loop
import Project.LebU32.Return

namespace Project.LebU32.Spec
open Wasm Project.Common Project.ProofKit Project.EulerRiemann.Execution PackedFloatFrame

theorem func0_encodes (env : HostEnv Unit) (initial : Store Unit) (seed : Heap) (input : UInt64)
    (hInput : input.toNat < 4294967296) (hHeap : seed.At initial) (hNodes : seed.nodes = [])
    (hFit : seed.top.toNat + 112 < 4294967296)
    (hMemory : seed.top.toNat + 112 ≤ initial.mem.pages * 65536)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.mem.pages ≤ initial.memoryCap «module» 0) :
    TerminatesWith env «module» 0 initial [.i64 0, .i64 0, .i64 0, .i64 input, .i64 10]
      (fun final values => ∃ bytes,
        bytes.data.toList = lebList 10 input ∧
        values = [.i64 (UInt64.ofNat (lebList 10 input).length),
          .i64 (bytePointer seed (lebList 10 input).length), .i64 (bytePointer seed (lebList 10 input).length)] ∧
        FinishedStorage seed initial final (lebList 10 input).length bytes) := by
  let entry : Locals :=
    { params := [.i64 10, .i64 input, .i64 0, .i64 0, .i64 0]
      locals := List.replicate 36 (.i64 0)
      values := [] }
  have hFrame : RunningFrame entry (UInt64.ofNat (10 - 0)) input (bytePointer seed 0) (UInt64.ofNat 0) := by
    refine ⟨?_, ?_, I64Values.replicate 36 0, rfl, ?_, ?_⟩
    all_goals simp [entry, bytePointer]
  have hInvariant : encodingInvariant seed initial input initial entry := by
    refine Or.inl ⟨0, input, ByteArray.empty, ?_, ?_, hFrame, RunningStorage.initial seed initial hHeap hNodes⟩
    · simp
    · exact lebList_length_pos 10 input (by decide)
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp «module» func0 _ initial entry env
  rw [loop_shape, List.append_assoc]
  have hPrefix : func0.take 4 = [.constI64 0, .localSet 5, .constI64 0, .localSet 9] := rfl
  rw [hPrefix]
  wp_packed_frame [entry, List.replicate_succ]
  change wp «module» ([.block 0 0 [.loop 0 0 loopCode]] ++ func0.drop 5) _ initial entry env
  apply loop_spec env seed initial initial input entry hInvariant (encoded_length_bound input hInput)
    hFit hMemory hPages hCap
  intro final result hFinished
  obtain ⟨bytes, hBytes, hResultFrame, hStorage⟩ := hFinished
  change wp «module» (func0.drop 5 ++ []) _ final result env
  apply return_spec env final result _ _ _ hResultFrame
  wp_run
  exact ⟨bytes, hBytes, by simp [func0Def], hStorage⟩

#print axioms func0_encodes
end Project.LebU32.Spec
