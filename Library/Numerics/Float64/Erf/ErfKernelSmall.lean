import LeanExe.ProofKit.RealErf
import LeanExe.ProofKit.PolyChecks

/-!
The approximation error of `s_erf.c`'s rational function on `|x| < 0.84375`, where `erf x` is
`x + x R (x²)` with `R = pp/qq` of degrees 4 and 5, as `Erf.erfSmall` holds its coefficients.
`R (z)` approximates `(erf x - x)/x = (2/√π) Σ (-1)^k z^k/(k! (2k + 1)) - 1`.  The check compares
`qq ((2/√π)_lo E (z) - 1) - pp` with `(5/8) 2^-55 qq` on `[0, 0.84375²]` through `PolyChecks`,
where `E` is the partial sum of 20 terms, and `erf_series` and `scale_bounds` add the remainder
and the width of the enclosure of `2/√π`.  The largest error, about `2^-55.86`, is at `z = 0`:
`pp0` is `2/√π - 1` rounded one unit below `efx`, which the source's stated `2^-57.90` leaves out.
-/

namespace Library.Numerics.Float64.Erf.ErfKernelSmall
open LeanExe.ProofKit PolyBound PolyChecks RealErf

/-- `pp0 + pp1 z + ... + pp4 z⁴`. -/
def erfPP : List ℚ :=
  [ratOfWord 0x3FC06EBA8214DB68, ratOfWord 0xBFD4CD7D691CB913, ratOfWord 0xBF9D2A51DBD7194F,
    ratOfWord 0xBF77A291236668E4, ratOfWord 0xBEF8EAD6120016AC]

/-- `1 + qq1 z + ... + qq5 z⁵`. -/
def erfQQ : List ℚ :=
  [1, ratOfWord 0x3FD97779CDDADC09, ratOfWord 0x3FB0A54C5536CEBA, ratOfWord 0x3F74D022C4D36B0F,
    ratOfWord 0x3F215DC9221C1A10, ratOfWord 0xBED09C4342A26120]

/-- The lower end of the enclosure of `2/√π`. -/
def kappaLo : ℚ := 333038747416263463341 / 2 ^ 68

/-- `qq (κ_lo E - 1) - pp`. -/
def smallA : List ℚ := subP (mulP erfQQ (subP (scaleP kappaLo (erfCoeffs 20)) [1])) erfPP

def smallEps : ℚ := (5 / 8) / 2 ^ 55

def smallM : ℚ := smallEps * (3 / 2)

def smallUp : List ℚ := addP (subP smallA (scaleP smallEps erfQQ)) [smallM]

def smallLo : List ℚ := subP (addP smallA (scaleP smallEps erfQQ)) [smallM]

theorem small_up_1 : check smallUp 0 (729 / 2048) smallM 18 = true := by decide +kernel
theorem small_up_2 : check smallUp (729 / 2048) (729 / 1024) smallM 18 = true := by decide +kernel
theorem small_lo_1 : check smallLo 0 (729 / 2048) smallM 18 = true := by decide +kernel
theorem small_lo_2 : check smallLo (729 / 2048) (729 / 1024) smallM 18 = true := by decide +kernel

theorem qq_check : check (subP erfQQ [116 / 100]) 0 (729 / 1024) (17 / 100) 18 = true := by
  decide +kernel

theorem series_check : check (subP (erfCoeffs 20) [17 / 20]) 0 (729 / 1024) (3 / 20) 18 = true := by
  decide +kernel

theorem kappaLo_cast : ((kappaLo : ℚ) : ℝ) = 333038747416263463341 / 2 ^ 68 := by
  simp [kappaLo]

theorem kappa_near : |scale - (kappaLo : ℝ)| ≤ 3 / 2 ^ 68 := by
  obtain ⟨h1, h2⟩ := scale_bounds
  rw [kappaLo_cast, abs_le]
  constructor <;> linarith

theorem qq_pos (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ 729 / 1024) : 99 / 100 ≤ eval erfQQ z := by
  have h := check_sound _ _ _ _ _ qq_check z (by simpa using hz0) (by norm_num; exact hz)
  rw [eval_subP] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at h
  have := (abs_le.mp h).1
  push_cast at this
  linarith

/-- The polynomial form: `|R (z) - (κ_lo E (z) - 1)| ≤ (5/8) 2^-55` on `[0, 0.84375²]`. -/
theorem small_poly (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ 729 / 1024) :
    |(kappaLo : ℝ) * eval (erfCoeffs 20) z - 1 - eval erfPP z / eval erfQQ z| ≤ smallEps := by
  have hup : Covers smallUp smallM 18 0 (729 / 1024) [729 / 2048] := ⟨small_up_1, small_up_2⟩
  have hlo : Covers smallLo smallM 18 0 (729 / 1024) [729 / 2048] := ⟨small_lo_1, small_lo_2⟩
  have hw := abs_le_weighted smallA erfQQ smallEps 0 (729 / 1024) smallM smallM
    (bounded_of_covers _ _ _ _ _ _ hup) (bounded_of_covers _ _ _ _ _ _ hlo) z
    (by simpa using hz0) (by norm_num; exact hz)
  have hq := qq_pos z hz0 hz
  have he : eval smallA z =
      ((kappaLo : ℝ) * eval (erfCoeffs 20) z - 1) * eval erfQQ z - eval erfPP z := by
    simp only [smallA, eval_subP, eval_mulP, eval_scaleP, eval_cons, eval_nil, mul_zero,
      add_zero, Rat.cast_one]
    ring
  rw [he] at hw
  exact sub_div_le _ _ _ _ (by linarith) hw

theorem series_bounds (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ 729 / 1024) :
    |eval (erfCoeffs 20) z| ≤ 1 := by
  have h := check_sound _ _ _ _ _ series_check z (by simpa using hz0) (by norm_num; exact hz)
  rw [eval_subP] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at h
  have h1 := abs_le.mp h
  push_cast at h1
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/-- The kernel's error relative to `|x|`: `|erf x - x - x R (x²)| ≤ (21/32) 2^-55 |x|` for
`|x| ≤ 0.84375`. -/
theorem small_kernel_error (x : ℝ) (hx : |x| ≤ 27 / 32) :
    |erf x - x - x * (eval erfPP (x ^ 2) / eval erfQQ (x ^ 2))| ≤
      |x| * ((21 / 32) / 2 ^ 55) := by
  have hz0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hz : x ^ 2 ≤ 729 / 1024 := by
    rw [← sq_abs]
    calc |x| ^ 2 ≤ (27 / 32) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
      _ = 729 / 1024 := by norm_num
  have hp := small_poly (x ^ 2) hz0 hz
  have hE := series_bounds (x ^ 2) hz0 hz
  have hk := kappa_near
  have hs := erf_series 20 x
  have hsc := scale_bounds
  have hax := abs_nonneg x
  have hpow : |x| ^ (2 * 20 + 1) ≤ |x| * (27 / 32) ^ 40 := by
    rw [show 2 * 20 + 1 = 40 + 1 by norm_num, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hax hx 40) hax
  have hrem : scale * (|x| ^ (2 * 20 + 1) / ((Nat.factorial 20 * (2 * 20 + 1) : ℕ) : ℝ)) ≤
      |x| * (1 / 2 ^ 70) := by
    have hf : ((Nat.factorial 20 * (2 * 20 + 1) : ℕ) : ℝ) = 99748982335242240000 := by
      norm_num [Nat.factorial]
    rw [hf]
    have h2 : scale ≤ 2 := by linarith [hsc.2]
    calc scale * (|x| ^ (2 * 20 + 1) / 99748982335242240000)
        ≤ 2 * ((|x| * (27 / 32) ^ 40) / 99748982335242240000) := by
          gcongr
      _ ≤ |x| * (1 / 2 ^ 70) := by
          rw [show 2 * ((|x| * (27 / 32) ^ 40) / 99748982335242240000) =
            |x| * (2 * (27 / 32) ^ 40 / 99748982335242240000) by ring]
          apply mul_le_mul_of_nonneg_left _ hax
          norm_num
  have hsplit : erf x - x - x * (eval erfPP (x ^ 2) / eval erfQQ (x ^ 2)) =
      (erf x - scale * (x * eval (erfCoeffs 20) (x ^ 2))) +
        x * ((scale - kappaLo) * eval (erfCoeffs 20) (x ^ 2)) +
        x * ((kappaLo : ℝ) * eval (erfCoeffs 20) (x ^ 2) - 1 -
          eval erfPP (x ^ 2) / eval erfQQ (x ^ 2)) := by ring
  rw [hsplit]
  have h2 : |x * ((scale - kappaLo) * eval (erfCoeffs 20) (x ^ 2))| ≤ |x| * (3 / 2 ^ 68) := by
    rw [abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_left _ hax
    calc |scale - kappaLo| * |eval (erfCoeffs 20) (x ^ 2)| ≤ (3 / 2 ^ 68) * 1 :=
          mul_le_mul hk hE (abs_nonneg _) (by norm_num)
      _ = 3 / 2 ^ 68 := mul_one _
  have h3 : |x * ((kappaLo : ℝ) * eval (erfCoeffs 20) (x ^ 2) - 1 -
      eval erfPP (x ^ 2) / eval erfQQ (x ^ 2))| ≤ |x| * smallEps := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hp hax
  have hsum := abs_add_three (erf x - scale * (x * eval (erfCoeffs 20) (x ^ 2)))
    (x * ((scale - kappaLo) * eval (erfCoeffs 20) (x ^ 2)))
    (x * ((kappaLo : ℝ) * eval (erfCoeffs 20) (x ^ 2) - 1 -
      eval erfPP (x ^ 2) / eval erfQQ (x ^ 2)))
  have heps : (smallEps : ℝ) = (5 / 8) / 2 ^ 55 := by simp [smallEps]
  rw [heps] at h3
  have hfin : |x| * (1 / 2 ^ 70) + |x| * (3 / 2 ^ 68) + |x| * ((5 / 8) / 2 ^ 55) ≤
      |x| * ((21 / 32) / 2 ^ 55) := by
    rw [← mul_add, ← mul_add]
    apply mul_le_mul_of_nonneg_left _ hax
    norm_num
  linarith [hs.trans hrem]

#print axioms small_poly
#print axioms small_kernel_error

end Library.Numerics.Float64.Erf.ErfKernelSmall
