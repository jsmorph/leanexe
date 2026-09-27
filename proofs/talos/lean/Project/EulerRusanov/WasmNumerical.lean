import Project.EulerRusanov.Numerical
import Project.EulerRusanov.Execution

/-!
# Numerical contract for exact generated-WAT execution

This layer composes two independently checked results.  `Execution` identifies
the complete return stack of generated function zero with the pure bit model
for every input.  `Numerical` proves that, whenever the raw-word guard accepts,
the model's three payload words are finite and satisfy componentwise absolute
real-error bounds.  Their composition makes the same claim about the exact
generated WebAssembly execution while retaining full store preservation.
-/

namespace Project.EulerRusanov.Spec

open Wasm

/-- WAT-level accepted-input numerical contract.  The returned raw words are
identified exactly with the total checked model; its status is zero and its
three payloads satisfy the independent real Euler--Rusanov error contract. -/
noncomputable def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (rhoL uL pL rhoR uR pR : UInt64),
    Model.eulerGuard rhoL uL pL rhoR uR pR = true →
    TerminatesWith env m 0 initial
      [.i64 pR, .i64 uR, .i64 rhoR, .i64 pL, .i64 uL, .i64 rhoL]
      (fun final values =>
        final = initial ∧
          values = Model.resultValues rhoL uL pL rhoR uR pR ∧
          (let result :=
            Model.checkedFluxBitsModel rhoL uL pL rhoR uR pR
           result.status = 0 ∧
             Numerical.FluxRealError rhoL uL pL rhoR uR pR
               { mass := result.mass
                 momentum := result.momentum
                 energy := result.energy }))

/-- Exact generated-WAT execution inherits the pure model's finite-result and
componentwise real-error theorem on every guard-accepted input. -/
theorem rusanovFluxCheckedBits_wat_real_error :
    RealErrorSpecFor Project.EulerRusanov.«module» := by
  intro env initial rhoL uL pL rhoR uR pR hGuard
  refine TerminatesWith.mono
    (rusanovFluxCheckedBits_exact env initial rhoL uL pL rhoR uR pR) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl,
    Numerical.checkedFluxBitsModel_real_error_of_guard hGuard⟩

#print axioms rusanovFluxCheckedBits_wat_real_error

end Project.EulerRusanov.Spec
