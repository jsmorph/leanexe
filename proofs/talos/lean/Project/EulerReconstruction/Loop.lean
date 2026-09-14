import Project.EulerReconstruction.LoopBody

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit

theorem limitInvariant.values {initial store : Store Unit} {center delta : State}
    {expected : Faces} {frame : Locals}
    (h : limitInvariant initial center delta expected store frame) : frame.values = [] := by
  obtain ⟨_, _, _, _, _, hFrame, _⟩ := h
  exact hFrame.values

theorem limitDone.values {initial store : Store Unit} {center delta : State}
    {expected : Faces} {frame : Locals}
    (h : limitDone initial center delta expected store frame) : frame.values = [] := by
  obtain ⟨_, _, _, _, _, hFrame, _⟩ := h
  exact hFrame.values

theorem limit_iteration_spec (env : HostEnv Unit) (initial store : Store Unit)
    (frame : Locals) (center delta : State) (expected : Faces)
    (hInv : limitInvariant initial center delta expected store frame) :
    wp Project.EulerReconstruction.«module» limitLoop
      (BlockLoop.stepPost (limitInvariant initial center delta expected)
        (limitDone initial center delta expected) (fun _ f => limitMeasure f)
        (limitMeasure frame)) store frame env := by
  obtain ⟨hStore, fuel, factor, output, done, hFrame, hExpected⟩ := hInv
  subst store
  rw [limit_guard_shape]
  refine FuelGuard.program_spec 0 20 _ env initial frame fuel (boolWord done)
    hFrame.values ?_ ?_ _ _ ?_
  · simp [Locals.get, hFrame.params, limitParams]
  · simpa [Locals.get, hFrame.params, limitParams, hFrame.locals] using hFrame.done
  · cases done
    · by_cases hFuel : fuel = 0
      · simp only [hFuel, true_or, ite_true]
        change limitDone initial center delta expected initial frame
        refine ⟨rfl, fuel, factor, output, false, hFrame, Or.inl hFuel, ?_⟩
        simpa [hFuel, limit] using hExpected
      · simp only [hFuel, boolWord, Bool.false_eq_true, ite_false, ne_eq,
          not_true_eq_false, or_self]
        simpa only [hExpected, Bool.false_eq_true, ite_false] using
          limit_body_spec env initial frame fuel center delta factor output hFrame hFuel
    · rw [ite_eq_left (Or.inr (by decide))]
      change limitDone initial center delta expected initial frame
      exact ⟨rfl, fuel, factor, output, true, hFrame, Or.inr rfl, hExpected⟩

theorem limit_loop_spec (env : HostEnv Unit) (initial store : Store Unit)
    (frame : Locals) (center delta : State) (expected : Faces)
    (hInv : limitInvariant initial center delta expected store frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      limitDone initial center delta expected final resultFrame →
      wp Project.EulerReconstruction.«module» rest Q final resultFrame env) :
    wp Project.EulerReconstruction.«module»
      ([.block 0 0 [.loop 0 0 limitLoop]] ++ rest) Q store frame env := by
  exact BlockLoop.program_spec _ env store frame limitLoop
    (limitInvariant initial center delta expected) (limitDone initial center delta expected)
    (fun _ f => limitMeasure f) (fun _ _ h => h.values) (fun _ _ h => h.values)
    hInv (fun st f h => limit_iteration_spec env initial st f center delta expected h)
    Q rest hNext

#print axioms limit_iteration_spec
#print axioms limit_loop_spec

end Project.EulerReconstruction.Execution
