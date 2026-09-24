import Project.EulerRiemann.FrozenNumericsSideResidual
import Project.EulerRiemann.FrozenExecutionSide

namespace Project.EulerRiemann.Frozen.SideResidual
open Wasm CodeLib.IEEE64

def Behavior (rho mx my energy : UInt64) : Prop :=
  let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
  let side := Numerics.sideCheckedBits rho mx my energy
  let bound := Numerics.sideErrorBounds rho mx my energy
  side.status = 0 →
    value side.massFlux = value mx ∧
    |value side.pressure - (2 / 5) * I| ≤ bound.pressure ∧
    |value side.momentumFlux - ((value mx)^2 / value rho + (2 / 5) * I)| ≤ bound.momentum ∧
    |value side.transverseFlux - value mx * value my / value rho| ≤ bound.transverse ∧
    |value side.energyFlux - (value energy + (2 / 5) * I) * (value mx / value rho)| ≤ bound.energy

def SpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64),
    TerminatesWith env m 22 initial [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = Execution.sideValues rho mx my energy ∧
        Behavior rho mx my energy)

theorem side_residual : SpecFor Project.EulerRiemann.Frozen.module := by
  intro env initial rho mx my energy
  refine TerminatesWith.mono (Execution.side_exact env initial rho mx my energy) ?_
  rintro final values ⟨hFinal, hValues⟩
  exact ⟨hFinal, hValues, Numerics.accepted_side_reference_bound rho mx my energy⟩

#print axioms side_residual
end Project.EulerRiemann.Frozen.SideResidual
