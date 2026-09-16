import Project.ProofKit.RealNormalization

namespace Project.ProofKit.RealNormBounds
open RealNormalization

theorem difference {n : Nat} (x y : Fin n → ℝ) :
    sumSquares (fun i => x i-y i) ≤ 2*sumSquares x+2*sumSquares y := by
  calc
    _ ≤ ∑ i, (2*(x i)^2+2*(y i)^2) :=
      Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg (x i+y i)])
    _ = _ := by simp [sumSquares, Finset.sum_add_distrib, Finset.mul_sum]

theorem dot {n : Nat} (x y : Fin n → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : sumSquares x ≤ a^2) (hy : sumSquares y ≤ b^2) :
    |∑ i, x i*y i| ≤ a*b := by
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg ha hb)).mp
  rw [sq_abs]
  calc
    _ ≤ sumSquares x*sumSquares y := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ a^2*b^2 := mul_le_mul hx hy (sumSquares_nonneg _) (sq_nonneg _)
    _ = _ := by ring

theorem matrix {m n : Nat} (w : Fin m → Fin n → ℝ) (y : Fin n → ℝ) :
    sumSquares (fun i => ∑ j, w i j*y j) ≤ (∑ i, sumSquares (w i))*sumSquares y := by
  calc
    _ ≤ ∑ i, sumSquares (w i)*sumSquares y :=
      Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    _ = _ := by rw [Finset.sum_mul]

theorem bilinear {m n : Nat} (w : Fin m → Fin n → ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : sumSquares x ≤ a^2) (hw : (∑ i, sumSquares (w i)) ≤ b^2)
    (hy : sumSquares y ≤ c^2) :
    |∑ i, ∑ j, x i*w i j*y j| ≤ a*b*c := by
  have hwy : sumSquares (fun i => ∑ j, w i j*y j) ≤ (b*c)^2 :=
    (matrix w y).trans ((mul_le_mul hw hy (sumSquares_nonneg _) (sq_nonneg _)).trans_eq (by ring))
  have hd := dot x (fun i => ∑ j, w i j*y j) a (b*c) ha (mul_nonneg hb hc) hx hwy
  simpa only [Finset.mul_sum, mul_assoc] using hd

theorem dot_center {n : Nat} (x c : Fin n → ℝ) (k : ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, x i*(c i-k)) = ∑ i, x i*c i := by
  simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx]

#print axioms bilinear
end Project.ProofKit.RealNormBounds
