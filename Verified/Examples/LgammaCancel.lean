import Verified.Examples.LgammaZerosB
import Verified.Examples.LgammaCancelTail

/-!
**`CancelFact`**: at every non-integer double `x ≤ -21/2`, `lgamma (1 - x) ≤ 2 ^ 32 |lgamma x|`.
Below -17 this is `LgammaCancelTail.cancel_tail`.  On `(-n - 1, -n)` for `n` from 11 to 16,
`LgammaZerosB` bounds `|lgamma x|` below at every double, and `lgamma (1 - x) ≤ lgamma 18 =
log 17! ≤ 49 log 2 < 49`.  On `(-11, -21/2]`, `LgammaZerosB.bound10cut` gives
`|lgamma x| ≥ 267 · 2 ^ -35`, and `lgamma (1 - x) ≤ lgamma 12 = log 11! < 26`, below
`2 ^ 32 · 267 · 2 ^ -35 ≈ 33.4`.
-/

namespace Verified.Examples.LgammaCancel

open Real LeanExe.ProofKit GammaBasic GammaThresholds RatExpLog CodeLib.IEEE64

/-- `lgamma (m + 1) = log m!` is at most `k` when `m! ≤ 2 ^ k`. -/
theorem lgamma_fact_le (m k : ℕ) (hk : ((Nat.factorial m : ℕ) : ℝ) ≤ 2 ^ k) :
    lgamma ((m : ℝ) + 1) ≤ k := by
  rw [lgamma, Real.Gamma_nat_eq_factorial]
  have h1 := Real.log_le_log (by positivity) hk
  rw [Real.log_pow] at h1
  have h2 : Real.log 2 < 1 := by
    have h4 := log_two_hi
    have h5 : (log2Hi : ℝ) < 1 := by norm_num [log2Hi]
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2.le (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  linarith

theorem lgamma_18 : lgamma 18 ≤ 49 := by
  have h := lgamma_fact_le 17 49 (by norm_num [Nat.factorial])
  norm_num at h
  exact h

theorem lgamma_12 : lgamma 12 ≤ 26 := by
  have h := lgamma_fact_le 11 26 (by norm_num [Nat.factorial])
  norm_num at h
  exact h

/-- **The cancellation of the reflection** from -21/2 down. -/
theorem cancel_fact (w : UInt64) (hv : value w ≤ -21 / 2) (hni : ∀ n : ℤ, value w ≠ n) :
    |lgamma (1 - value w)| ≤ 2 ^ 32 * |lgamma (value w)| := by
  rcases lt_or_ge (value w) (-17) with h17 | h17
  · exact LgammaCancelTail.cancel_tail w h17 hni
  have hgt : ∀ k : ℤ, (k : ℝ) ≤ value w → (k : ℝ) < value w := fun k hk =>
    lt_of_le_of_ne hk (fun h => hni k h.symm)
  have h17' := hgt (-17) (by push_cast; exact h17)
  push_cast at h17'
  have hpos : 0 ≤ lgamma (1 - value w) := by
    have := lgamma_mono (le_refl 2) (by linarith : (2 : ℝ) ≤ 1 - value w)
    rwa [lgamma_two] at this
  rw [abs_of_nonneg hpos]
  have h18 : lgamma (1 - value w) ≤ 49 :=
    (lgamma_mono (by linarith) (by linarith)).trans lgamma_18
  rcases lt_or_ge (value w) (-16) with h16 | h16
  · have hb := LgammaZerosB.bound16 w (by push_cast; linarith) (by push_cast; linarith)
    have hm : (49 : ℝ) / 2 ^ 32 ≤
        min ((471 / 2048) : ℝ) (min ((321 / 8192) : ℝ) (69 / 2048)) := by
      simp only [le_min_iff]; norm_num
    linarith
  have h16' := hgt (-16) (by push_cast; exact h16)
  push_cast at h16'
  rcases lt_or_ge (value w) (-15) with h15 | h15
  · have hb := LgammaZerosB.bound15 w (by push_cast; linarith) (by push_cast; linarith)
    have hm : (49 : ℝ) / 2 ^ 32 ≤ min (min ((69 / 2048) : ℝ) (449 / 131072))
        (min ((301 / 262144) : ℝ) (149 / 131072)) := by
      simp only [le_min_iff]; norm_num
    linarith
  have h15' := hgt (-15) (by push_cast; exact h15)
  push_cast at h15'
  rcases lt_or_ge (value w) (-14) with h14 | h14
  · have hb := LgammaZerosB.bound14 w (by push_cast; linarith) (by push_cast; linarith)
    have hm : (49 : ℝ) / 2 ^ 32 ≤ min (min ((149 / 131072) : ℝ) (301 / 262144))
        (min ((87 / 1048576) : ℝ) (291 / 4194304)) := by
      simp only [le_min_iff]; norm_num
    linarith
  have h14' := hgt (-14) (by push_cast; exact h14)
  push_cast at h14'
  rcases lt_or_ge (value w) (-13) with h13 | h13
  · have hb := LgammaZerosB.bound13 w (by push_cast; linarith) (by push_cast; linarith)
    have hm : (49 : ℝ) / 2 ^ 32 ≤ min (min ((291 / 4194304) : ℝ) (347 / 4194304))
        (min ((453 / 67108864) : ℝ) (277 / 67108864)) := by
      simp only [le_min_iff]; norm_num
    linarith
  have h13' := hgt (-13) (by push_cast; exact h13)
  push_cast at h13'
  rcases lt_or_ge (value w) (-12) with h12 | h12
  · have hb := LgammaZerosB.bound12 w (by push_cast; linarith) (by push_cast; linarith)
    have hm : (49 : ℝ) / 2 ^ 32 ≤ min (min ((277 / 67108864) : ℝ) (453 / 67108864))
        (min ((495 / 8589934592) : ℝ) (209 / 268435456)) := by
      simp only [le_min_iff]; norm_num
    linarith
  have h12' := hgt (-12) (by push_cast; exact h12)
  push_cast at h12'
  rcases lt_or_ge (value w) (-11) with h11 | h11
  · have hb := LgammaZerosB.bound11 w (by push_cast; linarith) (by push_cast; linarith)
    have hm : (49 : ℝ) / 2 ^ 32 ≤ min (min ((53 / 67108864) : ℝ) (405 / 8589934592))
        (min ((23 / 536870912) : ℝ) (231 / 8589934592)) := by
      simp only [le_min_iff]; norm_num
    linarith
  have h11' := hgt (-11) (by push_cast; exact h11)
  push_cast at h11'
  have hb := LgammaZerosB.bound10cut w (by push_cast; linarith) hv
  have h12l : lgamma (1 - value w) ≤ 26 :=
    (lgamma_mono (by linarith) (by linarith)).trans lgamma_12
  have hm : (26 : ℝ) / 2 ^ 32 ≤
      min ((267 / 34359738368) : ℝ) (min ((133 / 2147483648) : ℝ) (477 / 32)) := by
    simp only [le_min_iff]; norm_num
  linarith

#print axioms cancel_fact

end Verified.Examples.LgammaCancel
