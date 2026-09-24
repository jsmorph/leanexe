import Project.LocalRegion.Step
import Interpreter.Wasm.Wp.Defs

namespace Project.LocalRegion
open Wasm Project.FunctionRegion

private theorem exec_related_of_one
    (hOne : ∀ (env : HostEnv α) st source target inst,
      Related source target → PortableInstruction calls inst →
      AllowsInstruction domain inst →
      ContinuationRel Related (execOne fuel m st source inst env)
        (execOne fuel m st target (renameInstruction rename inst) env))
    (env : HostEnv α) (st : Store α) (source target : Locals) (program : Program)
    (hRelated : Related source target) (hPortable : PortableProgram calls program)
    (hAllowed : AllowsProgram domain program) :
    ContinuationRel Related (exec fuel m st source program env)
      (exec fuel m st target (renameProgram rename program) env) := by
  induction program generalizing st source target with
  | nil =>
      simp only [exec, renameProgram]
      exact .fallthrough hRelated
  | cons inst rest ih =>
      cases hPortable with
      | cons _ _ hInst hRest =>
          have hResult := hOne env st source target inst hRelated hInst hAllowed.1
          simp only [exec, renameProgram]
          generalize hSource : execOne fuel m st source inst env = sourceResult at hResult ⊢
          generalize hTarget :
            execOne fuel m st target (renameInstruction rename inst) env = targetResult at hResult ⊢
          cases hResult with
          | fallthrough h => exact ih _ _ _ h hRest hAllowed.2
          | «break» h => exact .break h
          | returned => exact .returned _ _
          | trap => exact .trap _ _
          | invalid => exact .invalid _
          | outOfFuel => exact .outOfFuel
          | returnCall => exact .returnCall _ _ _
          | throwing h => exact .throwing h

private theorem semantics_related (mapping : FrameMap rename domain Related) :
    ∀ fuel,
      (∀ (env : HostEnv α) st source target inst,
        Related source target → PortableInstruction calls inst →
        AllowsInstruction domain inst →
        ContinuationRel Related (execOne fuel m st source inst env)
          (execOne fuel m st target (renameInstruction rename inst) env)) ∧
      (∀ (env : HostEnv α) st source target program,
        Related source target → PortableProgram calls program →
        AllowsProgram domain program →
        ContinuationRel Related (exec fuel m st source program env)
          (exec fuel m st target (renameProgram rename program) env)) := by
  intro fuel
  induction fuel with
  | zero =>
      have hOne : ∀ (env : HostEnv α) st source target inst,
          Related source target → PortableInstruction calls inst →
          AllowsInstruction domain inst →
          ContinuationRel Related (execOne 0 m st source inst env)
            (execOne 0 m st target (renameInstruction rename inst) env) := by
        intro env st source target inst hRelated hPortable hAllowed
        cases hPortable <;> simp only [renameInstruction, execOne.eq_def]
        all_goals exact .outOfFuel
      exact ⟨hOne, exec_related_of_one hOne⟩
  | succ fuel ih =>
      have hOne := execOne_succ mapping ih.1 ih.2
      exact ⟨hOne, exec_related_of_one hOne⟩

theorem exec_related (mapping : FrameMap rename domain Related)
    (hRelated : Related source target) (hPortable : PortableProgram calls program)
    (hAllowed : AllowsProgram domain program) :
    ContinuationRel Related (exec fuel m st source program env)
      (exec fuel m st target (renameProgram rename program) env) :=
  (semantics_related mapping fuel).2 env st source target program hRelated hPortable hAllowed

theorem wp_transport (mapping : FrameMap rename domain Related)
    (hRelated : Related source target) (hPortable : PortableProgram calls program)
    (hAllowed : AllowsProgram domain program)
    (hPost : ∀ sourceResult targetResult, ContinuationRel Related sourceResult targetResult →
      P sourceResult → Q targetResult)
    (hSource : wp m program P st source env) :
    wp m (renameProgram rename program) Q st target env := by
  unfold wp at hSource ⊢
  obtain ⟨minimumFuel, hFuel⟩ := hSource
  exact ⟨minimumFuel, fun fuel hMinimum =>
    hPost _ _ (exec_related mapping hRelated hPortable hAllowed) (hFuel fuel hMinimum)⟩

#print axioms exec_related
#print axioms wp_transport
end Project.LocalRegion
