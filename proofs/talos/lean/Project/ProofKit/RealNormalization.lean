import Mathlib.Tactic
import Mathlib.Analysis.Real.Sqrt

namespace Project.ProofKit.RealNormalization

noncomputable def sumSquares {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, (x i)^2

noncomputable def squaredDistance {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  sumSquares (fun i => x i - y i)

theorem sumSquares_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ sumSquares x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem coordinate_square_le {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (x i)^2 ≤ sumSquares x :=
  Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

theorem distance_expansion {n : ℕ} (x y : Fin n → ℝ) :
    squaredDistance x y = sumSquares x + sumSquares y - 2 * ∑ i, x i * y i := by
  simp only [squaredDistance, sumSquares, sub_sq, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
  ring

theorem divided_distance {n : ℕ} (x y : Fin n → ℝ) (r s : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0) :
    r * s * squaredDistance (fun i => x i / r) (fun i => y i / s) =
      (s / r) * sumSquares x + (r / s) * sumSquares y - 2 * ∑ i, x i * y i := by
  have hi (i : Fin n) : r * s * (x i / r - y i / s)^2 =
      (s / r) * (x i)^2 + (r / s) * (y i)^2 - 2 * (x i * y i) := by
    field_simp
    ring
  change r * s * (∑ i, (x i / r - y i / s)^2) = _
  rw [Finset.mul_sum]
  simp only [hi, sumSquares,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem normalization_identity {n : ℕ} (x y : Fin n → ℝ) (r s epsilon dimension : ℝ)
    (hr : r ≠ 0) (hs : s ≠ 0)
    (hx : sumSquares x = dimension * (r^2 - epsilon))
    (hy : sumSquares y = dimension * (s^2 - epsilon)) :
    squaredDistance x y =
      r * s * squaredDistance (fun i => x i / r) (fun i => y i / s) +
        dimension * (r - s)^2 * (1 + epsilon / (r * s)) := by
  rw [divided_distance x y r s hr hs, distance_expansion, hx, hy]
  field_simp
  ring

theorem normalization_distance {n : ℕ} (x y : Fin n → ℝ) (r s epsilon dimension : ℝ)
    (hr : 0 < r) (hs : 0 < s) (he : 0 ≤ epsilon) (hd : 0 ≤ dimension)
    (hx : sumSquares x = dimension * (r^2 - epsilon))
    (hy : sumSquares y = dimension * (s^2 - epsilon)) :
    r * s * squaredDistance (fun i => x i / r) (fun i => y i / s) ≤
      squaredDistance x y := by
  rw [normalization_identity x y r s epsilon dimension (ne_of_gt hr) (ne_of_gt hs) hx hy]
  exact le_add_of_nonneg_right (by positivity)

#print axioms normalization_identity
#print axioms normalization_distance
end Project.ProofKit.RealNormalization
