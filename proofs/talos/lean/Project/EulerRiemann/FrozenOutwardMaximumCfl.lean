import Project.EulerRiemann.FrozenOutwardMaximumGrid
import Project.EulerRiemann.FrozenOutwardMeshSpec

namespace Project.EulerRiemann.Frozen.OutwardMaximum
open Project.Euler2DCellStep.Sweep (orient)
open Project.Euler2DConservative.Guard (decodedState)
open Project.Euler2DConservative.RealFlux (eigenvalues velocity soundSpeed)
open Traversal (Cell)
open CodeLib.IEEE64

theorem grid_characteristic_courant (grid : Array Cell) (n : Nat) (dt : UInt64)
    (hgrid : (gridUpper grid).status = 0)
    (hratio : (OutwardCfl.gridRatioChecked n dt (gridUpper grid).value).status = 0)
    (cell : Cell) (hc : cell ∈ grid) (axis : Bool) (i : Fin 4) :
    let state := orient axis cell.state
    value dt * (n : ℝ) * |eigenvalues
      (velocity (decodedState state.density state.mx state.my state.energy))
      (soundSpeed (decodedState state.density state.mx state.my state.energy)) i| ≤ (1 : ℝ) / 2 := by
  have hb := (grid_bounds grid hgrid).2 cell hc
  apply OutwardCfl.bounded_speed_grid_courant n dt (gridUpper grid).value hratio
  cases axis with
  | false => exact hb.1.2 i
  | true => exact hb.2.2 i

#print axioms grid_characteristic_courant

end Project.EulerRiemann.Frozen.OutwardMaximum
