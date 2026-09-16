import Project.EulerCertificate.TotalsSpec
import Project.EulerReconstructed.PhysicalStep
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

namespace Project.EulerCertificate.Totals
open Project.EulerRiemann.Traversal (Cell Indexed asGrid linearIndex_lt)
open Project.EulerRiemann.Conservation (gridTotal stateValue clamp_current)
open Project.Euler2DConservative.Guard (decodedState)
open Project.Euler2DCellStep.Sweep (State)
open scoped BigOperators

theorem stateValue_eq_decoded (q : State) (i : Fin 4) :
    stateValue q i = decodedState q.density q.mx q.my q.energy i := by
  fin_cases i <;> rfl

theorem realTotal_eq_sum (grid : Array Cell) (i : Fin 4) :
    realTotal grid i = ∑ k : Fin grid.size,
      decodedState grid[k.val].state.density grid[k.val].state.mx
        grid[k.val].state.my grid[k.val].state.energy i := by
  simpa only [realTotal, Vectors.listSum, Array.length_toList, Array.getElem_toList] using
    (Fin.sum_univ_fun_getElem grid.toList (fun cell : Cell =>
      decodedState cell.state.density cell.state.mx cell.state.my cell.state.energy i)).symm

theorem gridTotal_eq_sum {n : Nat} (hn : 0 < n) (grid : Array Cell) (i : Fin 4) :
    gridTotal hn (asGrid n grid) i =
      ∑ j : Fin n, ∑ k : Fin n, stateValue (asGrid n grid j k) i := by
  simp only [gridTotal, Finset.sum_range, clamp_current]

theorem realTotal_eq_gridTotal {n : Nat} (hn : 0 < n) (grid : Array Cell)
    (hg : Indexed n grid) (i : Fin 4) :
    realTotal grid i = gridTotal hn (asGrid n grid) i := by
  rw [realTotal_eq_sum, gridTotal_eq_sum]
  symm
  rw [← Fintype.sum_prod_type' (fun j k : Fin n => stateValue (asGrid n grid j k) i)]
  let e : Fin n × Fin n ≃ Fin grid.size := finProdFinEquiv.trans (finCongr hg.1.symm)
  apply Fintype.sum_equiv e
  intro ⟨j, k⟩
  have hb : j.val * n + k.val < grid.size := by
    rw [hg.1]
    exact linearIndex_lt n j k
  have he : (e (j, k)).val = j.val * n + k.val := by
    simp [e, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  have hs : asGrid n grid j k = grid[(e (j, k)).val].state := by
    simp only [asGrid, he, getElem!_pos grid (j.val * n + k.val) hb]
  rw [hs]
  exact stateValue_eq_decoded _ i

theorem physical_encloses_grid {n : Nat} (hn : 0 < n) (hmax : n ≤ 800)
    (grid : Array Cell) (hg : Indexed n grid) :
    Vectors.Valid (physical n grid) (Project.EulerReconstructed.Conservation.physicalTotal hn grid) := by
  have h := physical_valid n hmax grid
  intro i
  simpa only [Project.EulerReconstructed.Conservation.physicalTotal,
    realTotal_eq_gridTotal hn grid hg i] using h i

#print axioms realTotal_eq_gridTotal
#print axioms physical_encloses_grid
end Project.EulerCertificate.Totals
