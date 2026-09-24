import Project.EulerGridStep.CellReleaseCall
import Project.ProofKit.AliasGuards

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

/-- Owner aliases still live at each of the writer's five cleanup sites. -/
def writerProtected : Nat → List Nat
  | 5 => [65, 44, 42, 37, 35, 33, 28, 26, 24, 19, 17, 15, 13]
  | 4 => [65, 35, 33, 28, 26, 24, 19, 17, 15, 13]
  | 3 => [65, 26, 24, 19, 17, 15, 13]
  | 2 => [65, 17, 15, 13]
  | _ => [65]

/-- The writer's nonzero and nonaliasing conditional release. -/
def writerReleaseOne (pointerLocal : Nat) (kept : List Nat) : Wasm.Program :=
  [.localGet pointerLocal, .constI64 0, .eqI64, .eqz] ++
    AliasGuards.program pointerLocal kept ++ [.iff 0 0 [.localGet pointerLocal, .call 40] []]

/-- Conditional release preserves the caller's local frame and empties the call stack. -/
theorem writer_release_one_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (pointerLocal : Nat) (kept : List Nat) (pointer : UInt64) (P : Store Unit → Prop)
    (hValues : frame.values = []) (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hNonzero : pointer ≠ 0)
    (hKept : ∀ slot ∈ kept, ∃ other : UInt64, frame.get slot = some (.i64 other) ∧ pointer ≠ other)
    (hCall : TerminatesWith env m 40 initial [.i64 pointer]
      (fun final values => values = [] ∧ P final))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final, P final → wp m rest Q final frame env) :
    wp m (writerReleaseOne pointerLocal kept ++ rest) Q initial frame env := by
  simp only [writerReleaseOne, List.append_assoc, List.cons_append, List.nil_append, wp_localGet_cons,
    hPointer, hValues, wp_constI64_cons, wp_eqI64_cons, wp_eqz_cons, hNonzero]
  simp only [ite_false, ite_true]
  apply AliasGuards.distinct m env initial _ pointerLocal kept pointer rfl
    (by simpa using hPointer) (by simpa using hKept)
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
