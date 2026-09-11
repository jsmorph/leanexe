import LeanExe.Examples.EulerRiemann.Grid
import Init.Omega

namespace Project.EulerRiemann.Geometry
open LeanExe.Examples.EulerRiemann

theorem lowerFractionNumerator_le (n coordinate : Nat) :
    lowerFractionNumerator n coordinate ≤ 5 := by
  exact Nat.min_le_left _ _

theorem lowerFractionNumerator_full (n coordinate : Nat)
    (h : 5 * (coordinate + 1) ≤ 4 * n) :
    lowerFractionNumerator n coordinate = 5 := by
  unfold lowerFractionNumerator
  omega

theorem lowerFractionNumerator_empty (n coordinate : Nat)
    (h : 4 * n ≤ 5 * coordinate) :
    lowerFractionNumerator n coordinate = 0 := by
  unfold lowerFractionNumerator
  omega

theorem lowerFractionNumerator_cut (n coordinate : Nat)
    (hl : 5 * coordinate < 4 * n)
    (hr : 4 * n < 5 * (coordinate + 1)) :
    lowerFractionNumerator n coordinate = 4 * n - 5 * coordinate ∧
      0 < lowerFractionNumerator n coordinate ∧
      lowerFractionNumerator n coordinate < 5 := by
  unfold lowerFractionNumerator
  omega

theorem neighbor_backward_le (n index : Nat) (axisY : Bool) :
    neighbor n index axisY false ≤ index := by
  cases axisY <;> simp only [neighbor, Bool.false_eq_true, ↓reduceIte]
  all_goals split <;> omega

theorem neighbor_lt (n index : Nat) (axisY forward : Bool)
    (hn : 0 < n) (hi : index < n * n) :
    neighbor n index axisY forward < n * n := by
  have hrow : index / n < n := (Nat.div_lt_iff_lt_mul hn).mpr hi
  have hcol : index % n < n := Nat.mod_lt index hn
  have hsplit := Nat.mod_add_div index n
  cases forward with
  | false => exact Nat.lt_of_le_of_lt (neighbor_backward_le n index axisY) hi
  | true =>
    cases axisY with
    | false =>
      have hrowEnd : n * (index / n + 1) ≤ n * n :=
        Nat.mul_le_mul_left n (by omega)
      simp only [Nat.mul_add, Nat.mul_one] at hrowEnd
      simp only [neighbor, Bool.false_eq_true, ↓reduceIte]
      split <;> omega
    | true =>
      simp only [neighbor, ↓reduceIte]
      split
      · rename_i hnext
        have hrowEnd : n * (index / n + 2) ≤ n * n :=
          Nat.mul_le_mul_left n (by omega)
        simp only [Nat.mul_add, Nat.mul_two] at hrowEnd
        omega
      · exact hi

#print axioms neighbor_lt
#print axioms lowerFractionNumerator_cut

end Project.EulerRiemann.Geometry
