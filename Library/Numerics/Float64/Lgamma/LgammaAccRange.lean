import Library.Numerics.Float64.Lgamma.LgammaAsymSeries

/-!
The ranges of the two polynomials of `Lgamma.accurate` below 3.75 on `[-1/4, 1/4]`, from interval
enclosures of their Horner values on eight subintervals of `[0, 1/4]` for `p (v)` and `p (-v)`
(`val_neg`).  The polynomial at offset 68 of `accurateTable`, `log Γ (3/2 + d)`, lies in
`[-1/8, -0.08]` (`mid_range`), and the polynomial at offset 0, `log Γ (1 + t)/t`, lies in
`[-0.82, -0.38]` (`small_range`).  With `LgammaApprox.AccPolyFact` these bound `log Γ` away from
zero in the windows of the accurate path.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccRange
open LeanExe.ProofKit LgammaPolyIv LgammaAsymSeries Library.Numerics.Float64.Tgamma.TgammaPoly

set_option exponentiation.threshold 4096

/-- The coefficients of `p (-v)`. -/
def cqNeg (tab : Array UInt64) (o : ℕ) (k : ℕ) : ℚ := (-1) ^ k * cq tab o k

/-- The check of `valOk` for `p (-v)`. -/
def valNegOk (tab : Array UInt64) (o N P : ℕ) (X lo hi : ℚ) : Bool :=
  (List.range P).all fun p =>
    decide (lo ≤ (hornerIv (cqNeg tab o) N (X * p / P) (X * (p + 1) / P) (N - 1)).1) &&
    decide ((hornerIv (cqNeg tab o) N (X * p / P) (X * (p + 1) / P) (N - 1)).2 ≤ hi)

/-- **The value of the polynomial** on `[-X, 0]` lies in `[lo, hi]`. -/
theorem val_neg (tab : Array UInt64) (o N P : ℕ) (X lo hi : ℚ) (hP : 0 < P) (hN : 1 ≤ N)
    (hval : valNegOk tab o N P X lo hi = true) (v : ℝ) (hv0 : -(X : ℝ) ≤ v) (hv1 : v ≤ 0) :
    (lo : ℝ) ≤ PolyBound.eval (LgammaApprox.ddCoeffs tab o N) v ∧
      PolyBound.eval (LgammaApprox.ddCoeffs tab o N) v ≤ hi := by
  simp only [valNegOk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    at hval
  obtain ⟨p, hp, hpa, hpb⟩ := piece_cover (X : ℝ) P (-v) (by linarith) P hP
    (by rw [mul_div_assoc, div_self (by exact_mod_cast hP.ne'), mul_one]; linarith)
  have hX0 : (0 : ℚ) ≤ X := by exact_mod_cast (show (0 : ℝ) ≤ X by linarith)
  have he : horner (fun k => (cqNeg tab o k : ℝ)) N 0 (-v) (N - 1) =
      PolyBound.eval (LgammaApprox.ddCoeffs tab o N) v := by
    rw [horner_eval _ N hN, zero_mul, add_zero,
      show LgammaApprox.ddCoeffs tab o N = (List.range N).map (fun k =>
        LgammaApprox.q tab (o + 2 * k) + LgammaApprox.q tab (o + 2 * k + 1)) from rfl,
      Library.Numerics.Float64.Tgamma.TgammaWords.eval_map_range]
    apply Finset.sum_congr rfl
    intro k _
    have h1 : ((-1 : ℝ) ^ k) * ((-1) ^ k) = 1 := by rw [← mul_pow]; norm_num
    simp only [cqNeg, cq, LgammaApprox.q]
    push_cast
    rw [neg_pow v k]
    linear_combination (PolyBound.ratOfWord tab[o + 2 * k]! + PolyBound.ratOfWord tab[o + 2 * k + 1]! : ℝ) *
      v ^ k * h1
  obtain ⟨h1, h2⟩ := horner_iv (fun k => (cqNeg tab o k : ℝ)) (cqNeg tab o) N (fun _ _ => rfl)
    (X * p / P) (X * (p + 1) / P)
    (div_nonneg (mul_nonneg hX0 (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (-v) (by push_cast; exact hpa) (by push_cast; exact hpb) (N - 1) (by omega)
  obtain ⟨h3, h4⟩ := hval p hp
  rw [he] at h1 h2
  exact ⟨le_trans (by exact_mod_cast h3) h1, le_trans h2 (by exact_mod_cast h4)⟩

/-- **The value of the polynomial** on `[-X, X]` lies in `[lo, hi]`. -/
theorem val_sym (tab : Array UInt64) (o N P : ℕ) (X lo hi : ℚ) (hP : 0 < P) (hN : 1 ≤ N)
    (hpos : valOk tab o N P X lo hi = true) (hneg : valNegOk tab o N P X lo hi = true) (v : ℝ)
    (hv : |v| ≤ X) :
    (lo : ℝ) ≤ PolyBound.eval (LgammaApprox.ddCoeffs tab o N) v ∧
      PolyBound.eval (LgammaApprox.ddCoeffs tab o N) v ≤ hi := by
  rcases le_total 0 v with h | h
  · exact val_at tab o N P X lo hi hP hN hpos v h (by rw [abs_of_nonneg h] at hv; exact hv)
  · exact val_neg tab o N P X lo hi hP hN hneg v (by rw [abs_of_nonpos h] at hv; linarith) h

theorem mid_pos : valOk Lgamma.accurateTable 68 30 8 (1 / 4) (-1 / 8) (-2 / 25) = true := by
  decide +kernel

theorem mid_neg : valNegOk Lgamma.accurateTable 68 30 8 (1 / 4) (-1 / 8) (-2 / 25) = true := by
  decide +kernel

theorem small_pos : valOk Lgamma.accurateTable 0 34 8 (1 / 4) (-41 / 50) (-19 / 50) = true := by
  decide +kernel

theorem small_neg : valNegOk Lgamma.accurateTable 0 34 8 (1 / 4) (-41 / 50) (-19 / 50) = true := by
  decide +kernel

/-- **`log Γ (3/2 + d)`'s polynomial** lies in `[-1/8, -0.08]` for `|d| ≤ 1/4`. -/
theorem mid_range (d : ℝ) (hd : |d| ≤ 1 / 4) :
    -(1 / 8 : ℝ) ≤ PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) d ∧
      PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 68 30) d ≤ -(2 / 25) := by
  have h := val_sym Lgamma.accurateTable 68 30 8 (1 / 4) (-1 / 8) (-2 / 25) (by norm_num)
    (by norm_num) mid_pos mid_neg d (by push_cast; exact hd)
  push_cast at h
  constructor <;> linarith [h.1, h.2]

/-- **`log Γ (1 + t)/t`'s polynomial** lies in `[-0.82, -0.38]` for `|t| ≤ 1/4`. -/
theorem small_range (t : ℝ) (ht : |t| ≤ 1 / 4) :
    -(41 / 50 : ℝ) ≤ PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) t ∧
      PolyBound.eval (LgammaApprox.ddCoeffs Lgamma.accurateTable 0 34) t ≤ -(19 / 50) := by
  have h := val_sym Lgamma.accurateTable 0 34 8 (1 / 4) (-41 / 50) (-19 / 50) (by norm_num)
    (by norm_num) small_pos small_neg t (by push_cast; exact ht)
  push_cast at h
  constructor <;> linarith [h.1, h.2]

#print axioms mid_range
#print axioms small_range

end Library.Numerics.Float64.Lgamma.LgammaAccRange
