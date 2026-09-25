import Project.LebU32.Frames

namespace Project.LebU32.Spec
open Wasm Project.ProofKit PackedFloatFrame

def decisionCode : Wasm.Program := (loopCode.drop 7).take 28

theorem decision_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel value pointer length : UInt64) (hFrame : RunningFrame frame fuel value pointer length)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, BranchFrame result fuel value pointer length →
      wp «module» rest Q store
        { result with values := [.i32 (if value / 128 = 0 then 1 else 0)] } env) :
    wp «module» (decisionCode ++ rest) Q store frame env := by
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  have hTracker := hFrame.tracker
  have hDone := hFrame.done
  have hTrackerValue := (List.getElem_of_getElem? hTracker).2
  have hDoneValue := (List.getElem_of_getElem? hDone).2
  let result : Locals :=
    { params := [.i64 fuel, .i64 value, .i64 pointer, .i64 pointer, .i64 length]
      locals := (((((frame.locals.set 24 (.i64 value)).set 25 (.i64 128)).set 5
        (.i64 (value % 128))).set 24 (.i64 value)).set 25 (.i64 128)).set 6 (.i64 (value / 128))
      values := [] }
  have hResult : BranchFrame result fuel value pointer length := by
    refine ⟨⟨rfl, ?_, ?_, rfl, ?_, ?_⟩, ?_, ?_⟩
    · simp [result, hLocals]
    · exact (((((hFrame.typed.set _ _).set _ _).set _ _).set _ _).set _ _).set _ _
    all_goals simp [result, hLocals, hTrackerValue, hDoneValue]
  have hShape : decisionCode =
      [.localGet 1, .localSet 29, .constI64 128, .localSet 30,
       .localGet 30, .constI64 0, .eqI64,
       .iff 0 1 [.localGet 29] [.localGet 29, .localGet 30, .remUI64] [] [.i64], .localSet 10,
       .localGet 1, .localSet 29, .constI64 128, .localSet 30,
       .localGet 30, .constI64 0, .eqI64,
       .iff 0 1 [.constI64 0] [.localGet 29, .localGet 30, .divUI64] [] [.i64], .localSet 11,
       .localGet 11, .constI64 0, .eqI64,
       .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
       .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz] := rfl
  rw [hShape]
  wp_packed_frame [hParams, hLocals, hValues]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLocals]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLocals]
  by_cases hZero : value / 128 = 0
  · refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by simp [hZero])]
    wp_packed_frame [hParams, hLocals]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_packed_frame [hParams, hLocals]
    simpa [result, hZero] using hNext result hResult
  · refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simp [hZero])]
    wp_packed_frame [hParams, hLocals]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame [hParams, hLocals]
    simpa [result, hZero] using hNext result hResult

#print axioms decision_spec
end Project.LebU32.Spec
