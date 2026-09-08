import Project.EulerGridStep.CellReleaseCall

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- The writer's nonzero-pointer conditional release. -/
def writerReleaseOne (pointerLocal : Nat) : Wasm.Program :=
  [.localGet pointerLocal, .constI64 0, .eqI64, .eqz,
    .iff 0 0 [.localGet pointerLocal, .call 40] []]

/-- Conditional release preserves the caller's local frame and empties the call stack. -/
theorem writer_release_one_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (pointerLocal : Nat) (pointer : UInt64) (P : Store Unit → Prop)
    (hValues : frame.values = []) (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hNonzero : pointer ≠ 0)
    (hCall : TerminatesWith env m 40 initial [.i64 pointer]
      (fun final values => values = [] ∧ P final))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, P final → wp m rest Q final frame env) :
    wp m (writerReleaseOne pointerLocal ++ rest) Q initial frame env := by
  simp only [writerReleaseOne, List.cons_append, List.nil_append, wp_localGet_cons,
    hPointer, hValues, wp_constI64_cons, wp_eqI64_cons, wp_eqz_cons, hNonzero]
  simp only [ite_false, ite_true]
  apply wp_iff_cons rfl
  rw [ite_eq_left (by decide : (1 : UInt32) ≠ 0)]
  simp only [wp_localGet_cons, copyFrame_get_withValues, hPointer]
  refine wp_call_tw hCall ?_
  rintro final values ⟨rfl, hP⟩
  rw [wp_nil]
  simpa only [List.take_zero, List.drop_zero, List.nil_append,
    copyFrame_ofParts frame hValues] using hNext final hP

#print axioms writer_release_one_spec
end Project.EulerGridStep.Execution
