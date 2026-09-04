import Project.EulerRusanovStep.Program
import Project.EulerRusanovStep.Model

/-!
# Fixed two-cell Euler--Rusanov step specification

This intentionally incomplete proof root fixes the contract for the generated
no-argument entry.  The future execution theorem must establish the seven
pure-model words and complete store preservation for the actual generated WAT.
Until that theorem is proved, the source-driven case remains `complete: false`
and this module is not imported by the completed `Project` aggregate.
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

end Project.EulerRusanovStep.Spec
