import Project.EulerRiemann.OutwardSideSpec
import Project.EulerRiemann.NumericsSideResidual

namespace Project.EulerRiemann.OutwardNumerics
open CodeLib.IEEE64
open Numerics (sideErrorBounds)

theorem accepted_side_reference_bound (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    let I := value energy - ((value mx)^2 + (value my)^2) / (2 * value rho)
    let side := sideCheckedBits rho mx my energy
    let bound := sideErrorBounds rho mx my energy
    value side.massFlux = value mx ∧
    |value side.pressure - (2 / 5) * I| ≤ bound.pressure ∧
    |value side.momentumFlux - ((value mx)^2 / value rho + (2 / 5) * I)| ≤ bound.momentum ∧
    |value side.transverseFlux - value mx * value my / value rho| ≤ bound.transverse ∧
    |value side.energyFlux - (value energy + (2 / 5) * I) * (value mx / value rho)| ≤
      bound.energy := by
  have input := (side_bounds rho mx my energy h).1
  have bound := Numerics.physical_side_reference_bound rho mx my energy input
    (accepted_side_finite rho mx my energy h)
  dsimp only
  rw [side_values_of_accepted rho mx my energy h]
  exact ⟨rfl, bound⟩

#print axioms accepted_side_reference_bound
end Project.EulerRiemann.OutwardNumerics
