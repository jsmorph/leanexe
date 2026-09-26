import Project.LocalRegion.Step
import Interpreter.Wasm.Wp.Defs

namespace Project.LocalRegion
open Wasm Project.FunctionRegion

private theorem exec_of_one
    (frame : Frame slots localDomain)
    (hOne : ∀ (env : HostEnv α) st s t inst,
      frame.Related s t → PortableInstruction callDomain inst →
      AllowedInstruction localDomain inst →
      Continuations frame.Related (execOne fuel source st s inst env)
        (execOne fuel target st t (renameInstruction calls slots inst) env))
    (env : HostEnv α) (st : Store α) (s t : Locals) (program : Program)
    (hFrame : frame.Related s t)
    (hPortable : PortableProgram callDomain program)
    (hAllowed : AllowedProgram localDomain program) :
    Continuations frame.Related (exec fuel source st s program env)
      (exec fuel target st t (renameProgram calls slots program) env) := by
  induction program generalizing st s t with
  | nil => simpa only [renameProgram, exec] using Continuations.next st s t hFrame
  | cons inst rest ih =>
      cases hPortable with
      | cons _ _ hInst hRest =>
          simp only [renameProgram, exec]
          have h := hOne env st s t inst hFrame hInst hAllowed.1
          generalize execOne fuel source st s inst env = leftResult at h ⊢
          generalize execOne fuel target st t (renameInstruction calls slots inst) env = rightResult at h ⊢
          cases h with
          | next st' s' t' h' => exact ih st' s' t' h' hRest hAllowed.2
          | branch _ _ _ _ h' => exact .branch _ _ _ _ h'
          | returned => exact .returned _ _
          | trap => exact .trap _ _
          | invalid => exact .invalid _
          | exhausted => exact .exhausted
          | tail => exact .tail _ _ _
          | thrown _ _ _ _ _ h' => exact .thrown _ _ _ _ _ h'

theorem exec_related
    (frame : Frame slots localDomain)
    (shift : Shift source target calls types callDomain)
    (env : HostEnv α) (st : Store α) (s t : Locals) (program : Program)
    (hFrame : frame.Related s t)
    (hPortable : PortableProgram callDomain program)
    (hAllowed : AllowedProgram localDomain program) :
    Continuations frame.Related (exec fuel source st s program env)
      (exec fuel target st t (renameProgram calls slots program) env) := by
  suffices ∀ fuel,
      (∀ (env : HostEnv α) st s t inst,
        frame.Related s t → PortableInstruction callDomain inst →
        AllowedInstruction localDomain inst →
        Continuations frame.Related (execOne fuel source st s inst env)
          (execOne fuel target st t (renameInstruction calls slots inst) env)) ∧
      (∀ (env : HostEnv α) st s t program,
        frame.Related s t → PortableProgram callDomain program →
        AllowedProgram localDomain program →
        Continuations frame.Related (exec fuel source st s program env)
          (exec fuel target st t (renameProgram calls slots program) env)) from
    (this fuel).2 env st s t program hFrame hPortable hAllowed
  intro fuel
  induction fuel with
  | zero =>
      have hOne : ∀ (env : HostEnv α) st s t inst,
          frame.Related s t → PortableInstruction callDomain inst →
          AllowedInstruction localDomain inst →
          Continuations frame.Related (execOne 0 source st s inst env)
            (execOne 0 target st t (renameInstruction calls slots inst) env) := by
        intro env st s t inst _ _ _
        simp only [execOne.eq_def]
        exact .exhausted
      exact ⟨hOne, exec_of_one frame hOne⟩
  | succ fuel ih =>
      have hOne := execOne_succ frame shift.memory ih.1 ih.2
        (fun _ _ _ id h => FunctionRegion.run_eq shift id h (fuel := fuel))
      exact ⟨hOne, exec_of_one frame hOne⟩

/-- Transport total correctness and its fuel bound through a local layout. -/
theorem wp_transport
    (frame : Frame slots localDomain)
    (shift : Shift source target calls types callDomain)
    (env : HostEnv α) (st : Store α) (s t : Locals) (program : Program)
    (hFrame : frame.Related s t)
    (hPortable : PortableProgram callDomain program)
    (hAllowed : AllowedProgram localDomain program)
    (P Q : Assertion α)
    (hPost : ∀ a b, Continuations frame.Related a b → P a → Q b)
    (hSource : wp source program P st s env) :
    wp target (renameProgram calls slots program) Q st t env := by
  unfold wp at hSource ⊢
  obtain ⟨bound, hBound⟩ := hSource
  exact ⟨bound, fun fuel hFuel => hPost _ _
    (exec_related frame shift env st s t program hFrame hPortable hAllowed)
    (hBound fuel hFuel)⟩

#print axioms exec_related
#print axioms wp_transport
end Project.LocalRegion
