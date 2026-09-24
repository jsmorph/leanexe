import Project.ByteIO.Execution
import Project.ByteIO.ExecutionCasesModel

namespace Project.ByteIO
open Wasm

/-- `proc_exit` is the host's nonreturning controlled exit. Talos carries
its committed store in `Trap`; the named message distinguishes this model's
exit from an ordinary guest trap. The claim holds at every sufficient fuel. -/
def ExitsWith (env : HostEnv α) (m : Wasm.Module) (id : Nat)
    (initial : Store α) (post : Store α → Prop) : Prop :=
  ∃ n, ∀ fuel ≥ n, ∃ final, run fuel m id initial [] env = .Trap final "proc_exit" ∧ post final

theorem exits_of_check (env : HostEnv α) (m : Wasm.Module) (id : Nat)
    (initial : Store α) (fuel : Nat) (check : Store α → String → Bool)
    (post : Store α → Prop)
    (h : (match run fuel m id initial [] env with
      | .Trap final message => check final message
      | _ => false) = true)
    (hcheck : ∀ final message, check final message = true → message = "proc_exit" ∧ post final) :
    ExitsWith env m id initial post := by
  cases hr : run fuel m id initial [] env with
  | Trap final message =>
    obtain ⟨rfl, hp⟩ := hcheck final message (by simpa [hr] using h)
    refine ⟨fuel, fun n hn => ⟨final, ?_, hp⟩⟩
    rw [run_fuel_mono hn (by simp [hr])]
    exact hr
  | Success values final => simp [hr] at h
  | OutOfFuel => simp [hr] at h
  | Invalid message => simp [hr] at h
  | Thrown tag arguments final => simp [hr] at h

def exitCheck (st : Store World) (message : String) : Bool :=
  decide (message = "proc_exit") && decide (st.host.exited = some 0) &&
    caseCheck 0 [] exampleInput st [.i64 0]

set_option maxRecDepth 65536 in
set_option cbv.maxSteps 2000000 in
theorem echo_start_exits :
    ExitsWith partialHost Artifact.module 9 echoInitial
      (fun st => st.host.exited = some 0 ∧ CasePost 0 [] exampleInput st [.i64 0]) := by
  apply exits_of_check partialHost Artifact.module 9 echoInitial 32 exitCheck
  · cbv
  · intro st message h
    simp only [exitCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, caseCheck_sound _ _ _ _ _ h.2⟩

#print axioms exits_of_check
#print axioms echo_start_exits
end Project.ByteIO
