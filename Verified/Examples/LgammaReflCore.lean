import Verified.Examples.LgammaSinpiAbs
import Verified.Examples.LgammaFastPos
import Verified.Examples.TgammaAsym3
import Verified.Examples.TgammaFloor

/-!
The core of the fast path's reflection in `Lgamma.lgammaWith` for `x < -1/2`.  With `a = -x`, the
fractional part `φ = x - ⌊x⌋` (exact by Sterbenz's lemma, `refl_frac`), and `s = sin (π φ)/π`,
the reflection formula gives `ln |Γ x| = -(ln Γ a + ln (a s))` (`refl_L`).  The code computes `s`
(`asSinpipid`), `a s` (`mulDDD`), `ln (a s)` from the high part with the low part's quotient added
(`asLogd`), and the sum with `ln Γ a` from a positive leaf (`sumDD`).  `refl_core` bounds the
result's distance from `ln Γ a + ln (a s)` by the positive leaf's error, the sine's relative error
`ρ` (`2^-72` within `3/256` of an integer, `1.14 · 2^-71/s` elsewhere), `2 · 10^-21` for the
logarithm and the roundings, and the error of `sumDD`.
-/

namespace Verified.Examples.LgammaReflCore
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaWords LgammaFastSmall
  LgammaPiecePoly TgammaFloor

set_option exponentiation.threshold 4096

/-- **The reflection formula** for a negative non-integer `v`. -/
theorem refl_L (v : ℝ) (hv : v < 0) (hint : ∀ n : ℤ, v ≠ n) :
    Real.log (Real.Gamma v) = -(GammaBasic.lgamma (-v) +
      Real.log (-v * (Real.sin (Real.pi * Int.fract v) / Real.pi))) := by
  have hr := GammaBasic.lgamma_reflect hint
  have hnp : GammaBasic.NotPole (-v) :=
    GammaBasic.notPole_of_neg_one_lt (by linarith) (by linarith)
  have hadd := GammaBasic.lgamma_add_one hnp
  rw [show -v + 1 = 1 - v by ring] at hadd
  rw [hadd] at hr
  have hsp := GammaBasic.sin_pi_fract_pos hint
  have hlogs : Real.log (Real.sin (Real.pi * v)) =
      Real.log (Real.sin (Real.pi * Int.fract v)) := by
    rw [← Real.log_abs (Real.sin (Real.pi * v)), GammaBasic.sin_pi_eq, abs_mul, abs_zpow, abs_neg,
      abs_one, one_zpow, one_mul, abs_of_pos hsp]
  rw [hlogs] at hr
  have hl : Real.log (-v * (Real.sin (Real.pi * Int.fract v) / Real.pi)) =
      Real.log (-v) + (Real.log (Real.sin (Real.pi * Int.fract v)) - Real.log Real.pi) := by
    rw [Real.log_mul (by linarith) (div_pos hsp Real.pi_pos).ne',
      Real.log_div hsp.ne' Real.pi_pos.ne']
  rw [hl]
  rw [GammaBasic.lgamma] at hr
  linarith

/-- **The fractional part** `x - floorF x` of a double from `-2 ^ 52` to `-1/2`: exact, and
`n/2^53` with `0 < n < 2^53`. -/
theorem refl_frac (x : Float) (hx : Finite x.toBits) (h1 : -2 ^ 52 < value x.toBits)
    (h2 : value x.toBits < -1 / 2) (hint : ∀ n : ℤ, value x.toBits ≠ n) :
    Finite (floorF x).toBits ∧ value (floorF x).toBits = ⌊value x.toBits⌋ ∧
      Finite (x - floorF x).toBits ∧ value (x - floorF x).toBits = Int.fract (value x.toBits) ∧
      ∃ n : ℕ, 0 < n ∧ n < 2 ^ 53 ∧ Int.fract (value x.toBits) = n / 2 ^ 53 := by
  set v := value x.toBits with hvdef
  obtain ⟨hff, hfv⟩ := floorF_spec x hx (by rw [abs_of_neg (by linarith)]; linarith)
  have hfl1 : (⌊v⌋ : ℝ) ≤ v := Int.floor_le _
  have hfl2 : v < ⌊v⌋ + 1 := Int.lt_floor_add_one _
  have hfr : 0 < Int.fract v := Int.fract_pos.mpr (hint ⌊v⌋)
  have hfr1 : Int.fract v < 1 := Int.fract_lt_one _
  have hfd : Int.fract v = v - ⌊v⌋ := (Int.self_sub_floor _).symm
  have hfneg : (⌊v⌋ : ℝ) ≤ -1 := by
    have : ⌊v⌋ ≤ -1 := by
      rw [Int.floor_le_iff]; push_cast; linarith
    exact_mod_cast this
  have hd : |v - value (floorF x).toBits| = Int.fract v := by
    rw [hfv, ← hfd, abs_of_pos hfr]
  have hfx : Int.fract v ≤ -v := by
    rcases le_or_gt v (-1) with h | h
    · linarith
    · have : ⌊v⌋ = -1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      rw [hfd, this]; push_cast; linarith
  obtain ⟨hsf, hsv⟩ := F64Sterbenz.sub_exact x.toBits (floorF x).toBits hx hff
    (by rw [hd, abs_of_neg (by linarith)]; exact hfx)
    (by rw [hd, hfv, abs_of_neg (by linarith)]; linarith)
    (by rw [hfv, abs_of_neg (by linarith)]; linarith [(by norm_num : (2 : ℝ) ^ 52 + 1 < 2 ^ 1021)])
  rw [← F64Bits.toBits_sub] at hsf hsv
  refine ⟨hff, hfv, hsf, by rw [hsv, hfv, hfd], ?_⟩
  -- `v` lies on the spacing `2 ^ -53`
  obtain ⟨m, hm⟩ := LgammaFastMid.value_grid x.toBits
  set e := Wasm.IEEE64.exponent x.toBits with hedef
  have he : 1022 ≤ e := by
    by_contra hn
    have hhi := LgammaStir.binade_hi x.toBits e rfl (by omega)
    have : (2 : ℝ) ^ (e + 52) ≤ 2 ^ 1073 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (2 : ℝ) ^ (e + 52) / 2 ^ 1074 ≤ 2 ^ 1073 / 2 ^ 1074 :=
      div_le_div_of_nonneg_right this (by positivity)
    rw [abs_of_neg (by linarith)] at hhi
    have : (2 : ℝ) ^ 1073 / 2 ^ 1074 = 1 / 2 := by norm_num
    linarith
  have hv53 : v * 2 ^ 53 = (m : ℝ) * 2 ^ (e - 1022) := by
    have h5 : (0 : ℝ) < 2 ^ 1021 := by positivity
    apply mul_right_cancel₀ h5.ne'
    calc v * (2 : ℝ) ^ 53 * 2 ^ 1021 = v * (2 : ℝ) ^ 1074 := by rw [mul_assoc, ← pow_add]
      _ = (m : ℝ) * 2 ^ (e - 1) := hm
      _ = (m : ℝ) * 2 ^ (e - 1022) * 2 ^ 1021 := by rw [mul_assoc, ← pow_add]; congr 2; omega
  set N : ℤ := m * 2 ^ (e - 1022) - ⌊v⌋ * 2 ^ 53 with hNdef
  have hN : Int.fract v * 2 ^ 53 = N := by
    rw [hfd, sub_mul, hv53, hNdef]; push_cast; ring
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := by rw [← hN]; positivity
    exact_mod_cast this
  have hN1 : N < 2 ^ 53 := by
    have : (N : ℝ) < 2 ^ 53 := by
      rw [← hN]
      have := mul_lt_mul_of_pos_right hfr1 (by positivity : (0 : ℝ) < 2 ^ 53)
      linarith
    exact_mod_cast this
  refine ⟨N.toNat, by omega, by omega, ?_⟩
  rw [eq_div_iff (by positivity), hN]
  have : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hN0.le
  exact_mod_cast this.symm

#print axioms refl_L
#print axioms refl_frac

end Verified.Examples.LgammaReflCore
