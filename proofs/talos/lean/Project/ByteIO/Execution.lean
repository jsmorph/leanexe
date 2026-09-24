import Project.ByteIO.Artifact
import Project.ByteIO.ExecutionModel
import Interpreter.Wasm.Spec.Termination
import Lean.Elab.Tactic.Cbv

namespace Project.ByteIO
open Wasm

/-- Kernel-checked finite execution lifts to the ordinary fuel-independent
Talos theorem. Unlike a VM/native test, the check itself is a Lean proof. -/
theorem terminates_of_check (env : HostEnv α) (m : Wasm.Module) (id : Nat)
    (initial : Store α) (args : List Value) (fuel : Nat)
    (check : Store α → List Value → Bool) (post : Store α → List Value → Prop)
    (h : (match run fuel m id initial args env with
      | .Success values final => check final values
      | _ => false) = true)
    (hcheck : ∀ final values, check final values = true → post final values) :
    TerminatesWith env m id initial args post := by
  cases hr : run fuel m id initial args env with
  | Success values final =>
    apply TerminatesWith.of_run fuel values final hr
    apply hcheck
    simpa [hr] using h
  | OutOfFuel => simp [hr] at h
  | Trap final message => simp [hr] at h
  | Invalid message => simp [hr] at h
  | Thrown tag arguments final => simp [hr] at h

set_option maxRecDepth 65536 in
set_option cbv.maxSteps 2000000 in
theorem echo_partial_writes :
    TerminatesWith partialHost Artifact.module 6 echoInitial [] EchoPost := by
  apply terminates_of_check partialHost Artifact.module 6 echoInitial [] 32 echoCheck EchoPost
  · cbv
  · intro st values h
    simpa [echoCheck, EchoPost, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

#print axioms terminates_of_check
#print axioms partialHost_satisfies
#print axioms echo_partial_writes

end Project.ByteIO
