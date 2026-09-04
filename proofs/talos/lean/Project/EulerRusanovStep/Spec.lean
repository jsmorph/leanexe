import Project.EulerRusanovStep.Execution
import Project.EulerRusanovStep.Numerical

/-!
# Fixed two-cell Euler--Rusanov step specification

The registered theorem establishes the seven pure-model words and complete
store preservation for the actual generated WAT.  It is fuel-independent and
inherits the exact nine-call execution proof rather than substituting a
source-level evaluator for any generated function body.  The numerical layer
then decodes those exact words, proves finiteness and admissibility, and records
the signed cell and physical balance errors.
-/

namespace Project.EulerRusanovStep.Spec

open Wasm

/-- Fuel-independent exact execution contract for the fixed generated step. -/
def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit),
    TerminatesWith env m 6 initial []
      (fun final values =>
        final = initial ∧
          values = Project.EulerRusanovStep.Model.resultValues)

/-- Exact generated-WAT execution together with the decoded-real certificate
for the same pure-model result words. -/
noncomputable def RealSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit),
    TerminatesWith env m 6 initial []
      (fun final values =>
        final = initial ∧
          values = Project.EulerRusanovStep.Model.resultValues ∧
          Project.EulerRusanovStep.Numerical.RealCertificate
            Project.EulerRusanovStep.Model.sodQuarterStepCheckedBitsModel)

/-- The generated fixed step terminates with exactly the independent pure
binary64 model result and preserves the complete WebAssembly store. -/
theorem sodQuarterStepCheckedBits_exact :
    ExactSpecFor Project.EulerRusanovStep.«module» := by
  intro env initial
  exact func6_exact env initial

/-- The generated fixed step inherits the pure model's finite six-word
decoded result, exact signed cell errors, physical balance residual, and
two-cell Euler admissibility certificate. -/
theorem sodQuarterStepCheckedBits_wat_real :
    RealSpecFor Project.EulerRusanovStep.«module» := by
  intro env initial
  refine TerminatesWith.mono
    (sodQuarterStepCheckedBits_exact env initial) ?_
  rintro final values ⟨hfinal, hvalues⟩
  exact ⟨hfinal, hvalues,
    Project.EulerRusanovStep.Numerical.sodQuarterStepCheckedBitsModel_real⟩

#print axioms sodQuarterStepCheckedBits_exact
#print axioms sodQuarterStepCheckedBits_wat_real

end Project.EulerRusanovStep.Spec
