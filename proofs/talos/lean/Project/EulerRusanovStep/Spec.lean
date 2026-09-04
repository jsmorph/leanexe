import Project.EulerRusanovStep.Execution

/-!
# Fixed two-cell Euler--Rusanov step specification

The registered theorem establishes the seven pure-model words and complete
store preservation for the actual generated WAT.  It is fuel-independent and
inherits the exact nine-call execution proof rather than substituting a
source-level evaluator for any generated function body.
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

/-- The generated fixed step terminates with exactly the independent pure
binary64 model result and preserves the complete WebAssembly store. -/
theorem sodQuarterStepCheckedBits_exact :
    ExactSpecFor Project.EulerRusanovStep.«module» := by
  intro env initial
  exact func6_exact env initial

#print axioms sodQuarterStepCheckedBits_exact

end Project.EulerRusanovStep.Spec
