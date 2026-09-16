import Project.EulerCertificate.Totals
import Project.EulerCertificate.VectorsFold
import Project.EulerRiemann.TimeBounds

namespace Project.EulerCertificate.Totals
open Project.Euler2DConservative.Guard (decodedState)
open Project.EulerRiemann.Traversal (Cell)

noncomputable def realTotal (grid : Array Cell) : Fin 4 → ℝ :=
  Vectors.listSum grid.toList
    (fun cell => decodedState cell.state.density cell.state.mx cell.state.my cell.state.energy)

theorem sum_valid (grid : Array Cell) : Vectors.Valid (sum grid) (realTotal grid) := by
  have h := Vectors.foldl_valid grid.toList (fun cell => Vectors.state cell.state)
    (fun cell => decodedState cell.state.density cell.state.mx cell.state.my cell.state.energy)
    (fun cell _ => Vectors.state_valid cell.state) Vectors.zero (fun _ => 0) Vectors.zero_valid
  unfold sum addCell
  rw [← Array.foldl_toList]
  simpa only [realTotal, zero_add] using h

theorem physical_valid (n : Nat) (hn : n ≤ 800) (grid : Array Cell) :
    Vectors.Valid (physical n grid) (fun i => realTotal grid i / (n : ℝ) ^ 2) := by
  have h := ((sum_valid grid).divPositive (Project.EulerRiemann.Time.smallNaturalBits n)).divPositive
    (Project.EulerRiemann.Time.smallNaturalBits n)
  rw [Project.EulerRiemann.Time.smallNaturalBits_value n hn] at h
  simpa only [physical, div_div, pow_two] using h

#print axioms sum_valid
#print axioms physical_valid
end Project.EulerCertificate.Totals
