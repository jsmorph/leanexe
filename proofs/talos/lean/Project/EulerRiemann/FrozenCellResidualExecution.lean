import Project.EulerRiemann.FrozenNumericsCellResidual
import Project.EulerRiemann.FrozenExecutionCell

namespace Project.EulerRiemann.Frozen.CellResidual
open Wasm CodeLib.IEEE64
open Project.Euler2DCellStep.Sweep (Inputs)

def Behavior (ratio : UInt64) (q : Inputs) : Prop :=
  (Numerics.evaluate ratio q).status = 0 → ∀ i,
    let state := Numerics.stateWords q.center.density q.center.mx q.center.my q.center.energy i
    let left := Numerics.fluxWords (Numerics.leftFlux q) i
    let right := Numerics.fluxWords (Numerics.rightFlux q) i
    let out := Numerics.cellWords (Numerics.evaluate ratio q) i
    Project.ProofKit.F64ConservativeUpdate.Certificate ratio state left right out ∧
      value out - value state = value ratio * (value left - value right) + Numerics.cellUpdateResidual ratio q i ∧
      |Numerics.cellUpdateResidual ratio q i| ≤ Numerics.cellUpdateErrorBound ratio q i

def SpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (ratio : UInt64) (q : Inputs),
    TerminatesWith env m 65 initial
      [.i64 q.right.energy, .i64 q.right.my, .i64 q.right.mx, .i64 q.right.density,
        .i64 q.center.energy, .i64 q.center.my, .i64 q.center.mx, .i64 q.center.density,
        .i64 q.left.energy, .i64 q.left.my, .i64 q.left.mx, .i64 q.left.density, .i64 ratio]
      (fun final values => final = initial ∧
        values = Execution.cellStepValues ratio q.left.density q.left.mx q.left.my q.left.energy
          q.center.density q.center.mx q.center.my q.center.energy
          q.right.density q.right.mx q.right.my q.right.energy ∧ Behavior ratio q)

theorem cell_residual : SpecFor Project.EulerRiemann.Frozen.module := by
  intro env initial ratio q
  refine TerminatesWith.mono (Execution.cell_exact env initial ratio
    q.left.density q.left.mx q.left.my q.left.energy
    q.center.density q.center.mx q.center.my q.center.energy
    q.right.density q.right.mx q.right.my q.right.energy) ?_
  rintro final values ⟨hFinal, hValues⟩
  exact ⟨hFinal, hValues, Numerics.accepted_cell_balance ratio q⟩

#print axioms cell_residual
end Project.EulerRiemann.Frozen.CellResidual
