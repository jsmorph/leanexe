import Project.LebU32.Frames

namespace Project.LebU32.Spec
open Wasm Project.ProofKit PackedFloatFrame

theorem continueTail_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (fuel value previous length output : UInt64)
    (hFrame : AdvanceFrame frame fuel value previous length output)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, RunningFrame result (fuel - 1) (value / 128) output (length + 1) →
      wp «module» rest Q store result env) :
    wp «module» (continueByteCode.drop 75 ++ rest) Q store frame env := by
  have hParams := hFrame.params
  have hLocals := hFrame.locals
  have hValues := hFrame.values
  have hDone := hFrame.done
  have hQuotient := hFrame.quotient
  have hOwner := hFrame.owner
  have hPointer := hFrame.pointer
  have hLength := hFrame.length
  have hDoneValue := (List.getElem_of_getElem? hDone).2
  have hShape : continueByteCode.drop 75 =
      [.localGet 16, .localSet 24, .localGet 21, .localSet 25, .localGet 22, .localSet 26,
       .localGet 23, .localSet 27, .localGet 21, .localSet 28,
       .localGet 24, .localSet 1, .localGet 25, .localSet 2, .localGet 26, .localSet 3,
       .localGet 27, .localSet 4, .localGet 28, .localSet 5,
       .localGet 0, .constI64 1, .subI64, .localSet 0] := rfl
  rw [hShape]
  wp_packed_frame [hParams, hLocals, hValues, hQuotient, hOwner, hPointer, hLength]
  apply hNext
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_⟩
  · simp [hLocals]
  · exact (((((hFrame.typed.set _ _).set _ _).set _ _).set _ _).set _ _).set _ _
  all_goals simp [hLocals, hDoneValue]

#print axioms continueTail_spec
end Project.LebU32.Spec
