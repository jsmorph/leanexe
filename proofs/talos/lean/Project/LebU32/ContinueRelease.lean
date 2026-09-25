import Project.LebU32.Storage
import Project.LebU32.ContinueTail

namespace Project.LebU32.Spec
open Wasm Project.Runtime Project.ProofKit Project.EulerRiemann.Execution PackedFloatFrame

theorem continueRelease_spec (env : HostEnv Unit) (seed : Heap) (initial current : Store Unit)
    (frame : Locals) (fuel value : UInt64) (count : Nat) (bytes : ByteArray)
    (hFrame : AdvanceFrame frame fuel value (bytePointer seed count) (UInt64.ofNat count)
      (byteNode seed count).root)
    (hStorage : PushedStorage seed initial current count bytes (value % 128 + 128))
    (hCount : count ≤ 4) (hFit : seed.top.toNat + 112 < 4294967296)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final result,
      RunningFrame result (fuel - 1) (value / 128) (bytePointer seed (count + 1)) (UInt64.ofNat (count + 1)) →
      RunningStorage seed initial final (count + 1) (bytes.push (value % 128 + 128).toUInt8) →
      wp «module» rest Q final result env) :
    wp «module» (continueByteCode.drop 69 ++ rest) Q current frame env := by
  have hShape : continueByteCode.drop 69 = PackedReleaseGuard.program 5 21 5 ++ continueByteCode.drop 75 := rfl
  have hLength : UInt64.ofNat count + 1 = UInt64.ofNat (count + 1) := (UInt64.ofNat_add count 1).symm
  have hPointer : bytePointer seed (count + 1) = (byteNode seed count).root := by simp [bytePointer]
  have hTail (final : Store Unit)
      (hFinal : RunningStorage seed initial final (count + 1) (bytes.push (value % 128 + 128).toUInt8)) :
      wp «module» (continueByteCode.drop 75 ++ rest) Q final frame env := by
    apply continueTail_spec env final frame fuel value (bytePointer seed count) (UInt64.ofNat count)
      (byteNode seed count).root hFrame
    intro result hResult
    apply hNext final result
    · simpa only [hLength, hPointer] using hResult
    · exact hFinal
  rw [hShape, List.append_assoc]
  by_cases hZero : count = 0
  · subst count
    have hTracker : frame.locals[0]? = some (.i64 0) := hFrame.tracker
    have hParams := hFrame.params
    have hLocals := hFrame.locals
    have hValues := hFrame.values
    simp only [PackedReleaseGuard.program, List.cons_append, List.nil_append]
    wp_packed_frame [hParams, hLocals, hValues, hTracker, bytePointer]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame [hParams, hLocals]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame [hParams, hLocals]
    have hRestore : ({ frame with
      params := [.i64 fuel, .i64 value, .i64 0, .i64 0, .i64 (UInt64.ofNat 0)]
      values := [] } : Locals) = frame :=
      Frame.ext _ _ (by simpa [bytePointer] using hParams.symm) rfl hValues.symm
    rw [hRestore]
    exact hTail current hStorage.first
  · have hPositive : 0 < count := by omega
    have hOld := hStorage.previous hPositive
    have hSource : frame.get 5 = some (.i64 (byteNode seed (count - 1)).root) := by
      simpa [Locals.get, hFrame.params, hFrame.locals, bytePointer, hZero] using hFrame.tracker
    have hRetained : frame.get 21 = some (.i64 (byteNode seed count).root) := by
      simpa [Locals.get, hFrame.params, hFrame.locals] using hFrame.owner
    have hSep := byteNode_previous_separate seed count hCount hPositive hFit
    have hNe := hOld.root_ne (other := byteNode seed count) (by
      simp only [regionsDisjoint] at hSep ⊢
      omega)
    apply PackedReleaseGuard.program_spec env «module» 5 current (finishedHeap seed (count + 1)) frame
      (byteNode seed (count - 1)) bytes (byteNode seed count).root 5 21 (typeIdx := some 5)
      rfl rfl hStorage.heap hOld hFrame.values hSource hRetained hNe
    intro _
    exact hTail _ (hStorage.released hCount hPositive hFit)

#print axioms continueRelease_spec
end Project.LebU32.Spec
