import Library.Numerics.Float64.Lgamma.LgammaRootPath
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
**The cancellation of the reflection from -32 down.**  At a non-integer double `v ≤ -32`, the
reflection `log |Γ v| = log π - log |sin (π v)| - log Γ (1 - v)` loses at most a factor of 2:
`v` is a multiple of `2^-47`, so `|sin (π v)| ≥ 2^-46` and `0 ≤ log π - log |sin (π v)| ≤ 34.15`,
while `log Γ (1 - v) ≥ log 32! ≥ 69` (`cancel_double`).  From `-21/2` to `-32`,
`LgammaApprox.CancelFact` bounds the cancellation by `2^32` instead.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccCancel
open Real LeanExe.ProofKit GammaBasic CodeLib.IEEE64

/-- `log Γ 33 = log 32! ≥ 69`. -/
theorem lgamma_33 : 69 ≤ GammaBasic.lgamma 33 := by
  unfold GammaBasic.lgamma
  have h : Gamma 33 = (Nat.factorial 32 : ℝ) := by
    rw [show (33 : ℝ) = (32 : ℕ) + 1 by norm_num, Gamma_nat_eq_factorial]
  rw [h]
  have hf : (2 : ℝ) ^ 100 ≤ (Nat.factorial 32 : ℝ) := by
    have : 2 ^ 100 ≤ Nat.factorial 32 := by decide +kernel
    exact_mod_cast this
  have hl := Real.log_le_log (by positivity) hf
  rw [Real.log_pow] at hl
  have := Real.log_two_gt_d9
  push_cast at hl
  norm_num at this
  linarith

/-- **The reflection at `v ≤ -32`** cancels by at most 2, given the distance from `v` to the
integers. -/
theorem cancel32 (v : ℝ) (hv : v ≤ -32) (hint : ∀ n : ℤ, v ≠ n)
    (hd : 1 / 2 ^ 47 ≤ |v - round v|) :
    GammaBasic.lgamma (1 + |v|) ≤ 2 * |GammaBasic.lgamma v| ∧ 69 ≤ GammaBasic.lgamma (1 + |v|) := by
  have hav : |v| = -v := abs_of_neg (by linarith)
  rw [hav, show 1 + -v = 1 - v by ring]
  have hT : 69 ≤ GammaBasic.lgamma (1 - v) := by
    have hm := Gamma_strictMonoOn_Ici.monotoneOn (show (33 : ℝ) ∈ Set.Ici 2 by
      rw [Set.mem_Ici]; norm_num) (show 1 - v ∈ Set.Ici 2 by rw [Set.mem_Ici]; linarith)
      (by linarith : (33 : ℝ) ≤ 1 - v)
    have h33 := lgamma_33
    unfold GammaBasic.lgamma at h33 ⊢
    have := Real.log_le_log (Gamma_pos_of_pos (by norm_num)) hm
    linarith
  have hR := lgamma_reflect hint
  have hs := two_mul_abs_sub_round_le v
  have hs0 : 1 / 2 ^ 46 ≤ |sin (π * v)| := by linarith
  have hs1 : |sin (π * v)| ≤ 1 := abs_sin_le_one _
  have hls0 : Real.log (sin (π * v)) ≤ 0 := by
    rw [← Real.log_abs]
    exact Real.log_nonpos (abs_nonneg _) hs1
  have hls1 : -32 ≤ Real.log (sin (π * v)) := by
    rw [← Real.log_abs]
    have h1 := Real.log_le_log (by positivity) hs0
    rw [one_div, Real.log_inv, Real.log_pow] at h1
    have := Real.log_two_lt_d9
    norm_num at this h1 ⊢
    linarith
  have hpi1 : 0 ≤ Real.log π := Real.log_nonneg (by linarith [pi_gt_three])
  have hpi2 : Real.log π ≤ 43 / 20 := by
    have := Real.log_le_sub_one_of_pos pi_pos
    linarith [pi_lt_d2]
  have hneg : GammaBasic.lgamma v < 0 := by linarith
  rw [abs_of_neg hneg]
  constructor <;> linarith

/-- **The cancellation at a double `v ≤ -32`**: the double is a multiple of `2^-47`. -/
theorem cancel_double (sx : Float) (hsx : Finite sx.toBits) (h32 : value sx.toBits ≤ -32)
    (hint : ∀ n : ℤ, value sx.toBits ≠ n) :
    GammaBasic.lgamma (1 + |value sx.toBits|) ≤ 2 * |GammaBasic.lgamma (value sx.toBits)| ∧
      69 ≤ GammaBasic.lgamma (1 + |value sx.toBits|) := by
  apply cancel32 _ h32 hint
  obtain ⟨K, hK⟩ := LgammaRootPath.grid_p sx.toBits hsx 5 (by norm_num)
    (by rw [abs_of_neg (by linarith)]; norm_num; linarith)
  set m : ℤ := K - 2 ^ 47 * round (value sx.toBits) with hm
  have hdiff : value sx.toBits - round (value sx.toBits) = m / 2 ^ 47 := by
    rw [hm, hK]
    push_cast
    field_simp
    ring
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, zero_div, sub_eq_zero] at hdiff
    exact hint _ hdiff
  rw [hdiff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 47)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
  have h' : ((1 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at h'
  exact h'

end Library.Numerics.Float64.Lgamma.LgammaAccCancel
