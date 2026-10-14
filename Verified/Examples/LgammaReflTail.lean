import Verified.Examples.LgammaReflCore
import LeanExe.ProofKit.GammaThresholds

/-!
`FastSpec` for the reflection of `Lgamma.lgammaWith` from `x = -6` down to `-2 ^ 52`.  Within
`3/256` of an integer the sine has `2 ^ -72` relative, and the absolute form holds: the positive
leaf leaves a margin of `|fh|/2^67` under `2 eps`, and `|fh| ≥ 4` there.  Farther from the integers
`s = sin (π φ)/π ≥ 1/135`, `ln Γ |x| ≥ ln 64`, and `ln |Γ x| = -(ln Γ |x| + ln (|x| s))` is at least
a tenth of `ln Γ |x|` in magnitude, so the relative form holds (`refl_tail`).
-/

namespace Verified.Examples.LgammaReflTail
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaWords LgammaFastSmall
  LgammaPiecePoly TgammaFloor LgammaWalk LgammaReflCore

set_option exponentiation.threshold 4096

theorem c8_bounds : (799 / 10 ^ 24 : ℚ) ≤ PolyBound.ratOfWord 0x3B8E392010175EE6 ∧
    PolyBound.ratOfWord 0x3B8E392010175EE6 ≤ 801 / 10 ^ 24 := by
  decide +kernel

/-- The code's `eps + |lh| c8` within `2 ^ -52` of `eps + |lh| c8`. -/
theorem eps8_value (eps lh : Float) (he : Finite eps.toBits) (hl : Finite lh.toBits)
    (heb : |value eps.toBits| ≤ 2 ^ 900) (hlb : |value lh.toBits| ≤ 43) :
    Finite (eps + lh.abs * Float.ofBits 0x3B8E392010175EE6).toBits ∧
      |value (eps + lh.abs * Float.ofBits 0x3B8E392010175EE6).toBits -
        (value eps.toBits + |value lh.toBits| *
          ((PolyBound.ratOfWord 0x3B8E392010175EE6 : ℚ) : ℝ))| ≤
        (|value eps.toBits| + 1 / 2 ^ 60) / 2 ^ 52 := by
  obtain ⟨haf, hav⟩ := SinhWords.abs_float lh hl
  have hw : Wasm.IEEE64.isFinite 0x3B8E392010175EE6 = true := by decide
  have hc := qcast_le c8_bounds.1
  have hc' := qcast_le c8_bounds.2
  push_cast at hc hc'
  have ha := fapprox_self lh.abs haf
  have hb := fapprox_self (Float.ofBits 0x3B8E392010175EE6) (ofBits_finite _ hw)
  rw [hav] at ha
  rw [ofBits_value _ hw] at hb
  have hca : |((PolyBound.ratOfWord 0x3B8E392010175EE6 : ℚ) : ℝ)| ≤ 801 / 10 ^ 24 := by
    rw [abs_of_pos (by linarith)]; exact hc'
  have hm := fapprox_mul ha hb 43 (801 / 10 ^ 24) (by rw [abs_abs]; exact hlb) hca
    (43 * (801 / 10 ^ 24)) (by norm_num) (by norm_num)
  have hp : |(|value lh.toBits| * ((PolyBound.ratOfWord 0x3B8E392010175EE6 : ℚ) : ℝ))| ≤
      43 * (801 / 10 ^ 24) := by
    rw [abs_mul, abs_abs]; exact mul_le_mul hlb hca (abs_nonneg _) (by norm_num)
  have hs := fapprox_add (fapprox_self eps he) hm (|value eps.toBits| + 1 / 2 ^ 60)
    (by
      have := abs_add_le (value eps.toBits)
        (|value lh.toBits| * ((PolyBound.ratOfWord 0x3B8E392010175EE6 : ℚ) : ℝ))
      linarith [(by norm_num : (43 : ℝ) * (801 / 10 ^ 24) + (0 * (801 / 10 ^ 24) + 43 * 0 + 0 * 0 +
        43 * (801 / 10 ^ 24) / 2 ^ 53 + 1 / 2 ^ 1075) ≤ 1 / 2 ^ 60)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 900 + 1 / 2 ^ 60 < 2 ^ 1023)])
  refine ⟨hs.1, hs.2.trans ?_⟩
  have : (43 : ℝ) * (801 / 10 ^ 24) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 60 / 2 ^ 53 := by norm_num
  have h0 : 0 ≤ |value eps.toBits| := abs_nonneg _
  linarith

theorem log_bounds : (13862 / 10000 : ℝ) ≤ Real.log 4 ∧ Real.log 135 ≤ 4908 / 1000 ∧
    (4158 / 1000 : ℝ) ≤ Real.log 64 := by
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  · rw [show (135 : ℝ) = 2 ^ 7 * (135 / 128) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 135 / 128 by norm_num)
    push_cast; linarith
  · rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; linarith

theorem lgamma_six : Real.log 64 ≤ GammaBasic.lgamma 6 := by
  rw [GammaBasic.lgamma, show (6 : ℝ) = (5 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  exact Real.log_le_log (by norm_num) (by simp [Nat.factorial]; norm_num)

set_option maxHeartbeats 2000000 in
/-- **The reflection from -6 down**: `FastSpec` for `-(fh + fl + lh + ll')` with
`eps' = eps + 8 · 10^-22 |lh|`, given a positive leaf at `|x|` with the margin `|fh|/2^67`. -/
theorem refl_tail (hF : FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (x : Float) (hx : Finite x.toBits)
    (h6 : value x.toBits ≤ -6) (h52 : -2 ^ 52 < value x.toBits)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (fh fl eps : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (he : Finite eps.toBits) (hfh4 : 4 ≤ |value fh.toBits|)
    (hfhb : |value fh.toBits| ≤ 2 ^ 60)
    (hflb : |value fl.toBits| ≤ |value fh.toBits| / 2 ^ 17 + 1 / 2 ^ 38)
    (helo : |value fh.toBits| * (448 / 10 ^ 22) ≤ value eps.toBits)
    (hehi : value eps.toBits ≤ |value fh.toBits| / 2 ^ 62 + 1 / 2 ^ 78)
    (hpos : |GammaBasic.lgamma (-value x.toBits) - (value fh.toBits + value fl.toBits)| +
      |value fh.toBits| / 2 ^ 67 ≤ 2 * value eps.toBits)
    (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD fh fl C.1 (C.2 + B.2 / B.1)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  obtain ⟨hC1, hD1, hD2, hlh, hD1b, hlhL, hD2b, ρ, hρ, hcore⟩ := refl_core hF hL hS x hx h52
    (by linarith) hint fh fl hfh hfl (by linarith [(by norm_num : (2 : ℝ) ^ 60 ≤ 2 ^ 897)])
    (by linarith [(by norm_num : (2 : ℝ) ^ 60 / 2 ^ 17 + 1 / 2 ^ 38 ≤ 2 ^ 700)]) A B C D hA hB hC hD
  have he0 : 0 < value eps.toBits := by
    have : (0 : ℝ) < 4 * (448 / 10 ^ 22) := by norm_num
    have := mul_le_mul_of_nonneg_right hfh4 (by norm_num : (0 : ℝ) ≤ 448 / 10 ^ 22)
    linarith
  obtain ⟨he'f, he'v⟩ := eps8_value eps C.1 he hC1
    (by rw [abs_of_pos he0]; linarith [(by norm_num : (2 : ℝ) ^ 60 / 2 ^ 62 + 1 / 2 ^ 78 ≤ 2 ^ 900)])
    hlh
  rw [abs_of_pos he0] at he'v
  have hLr := refl_L (value x.toBits) (by linarith) hint
  set v := value x.toBits with hvdef
  set φ := Int.fract v with hφdef
  set s := Real.sin (Real.pi * φ) / Real.pi with hsdef
  set a := -v with hadef
  set lg := GammaBasic.lgamma a with hlgdef
  set F := value fh.toBits with hFdef
  set c8 := ((PolyBound.ratOfWord 0x3B8E392010175EE6 : ℚ) : ℝ) with hc8def
  have hc8 := qcast_le c8_bounds.1
  have hc8' := qcast_le c8_bounds.2
  push_cast at hc8 hc8'
  rw [← hc8def] at hc8 hc8'
  set e' := eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6 with he'def
  have hlhc : 0 ≤ |value C.1.toBits| * c8 := mul_nonneg (abs_nonneg _) (by linarith)
  have hlhc' : |value C.1.toBits| * c8 ≤ 43 * (801 / 10 ^ 24) :=
    mul_le_mul hlh hc8' (by linarith) (by norm_num)
  have he'lo : value eps.toBits - (value eps.toBits + 1 / 2 ^ 60) / 2 ^ 52 ≤ value e'.toBits := by
    have := abs_le.mp he'v; linarith
  have he'hi : value e'.toBits ≤ value eps.toBits + 43 * (801 / 10 ^ 24) +
      (value eps.toBits + 1 / 2 ^ 60) / 2 ^ 52 := by
    have := abs_le.mp he'v; linarith
  obtain ⟨hn1f, hn1v⟩ := LgammaFastTiny.neg_float D.1 hD1
  obtain ⟨hn2f, hn2v⟩ := LgammaFastTiny.neg_float D.2 hD2
  have hFabs : |F| ≥ 4 := hfh4
  have hsum : (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) /
      2 ^ 53 ≤ |F| * (3 / 2 ^ 70 + 1 / 2 ^ 103) + 1 / 2 ^ 71 := by
    have h1 : |value D.1.toBits| / 2 ^ 52 ≤
        ((|F| + 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 :=
      div_le_div_of_nonneg_right hD1b (by norm_num)
    have h2 : (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) /
        2 ^ 53 ≤ (3 * (|F| / 2 ^ 17 + 1 / 2 ^ 38 + 1 / 2 ^ 20) +
          ((|F| + 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith
    have h3 : (3 * (|F| / 2 ^ 17 + 1 / 2 ^ 38 + 1 / 2 ^ 20) +
        ((|F| + 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 =
        |F| * (3 / 2 ^ 70 + (1 + 1 / 2 ^ 51) / 2 ^ 105) +
          (3 * (1 / 2 ^ 38 + 1 / 2 ^ 20) + (43 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 +
            1 / 2 ^ 1074) / 2 ^ 53 := by ring
    have h4 : |F| * (3 / 2 ^ 70 + (1 + 1 / 2 ^ 51) / 2 ^ 105) ≤ |F| * (3 / 2 ^ 70 + 1 / 2 ^ 103) :=
      mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _)
    have h5 : (3 * (1 / 2 ^ 38 + 1 / 2 ^ 20) + (43 * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 52 +
        1 / 2 ^ 1074) / 2 ^ 53 ≤ (1 : ℝ) / 2 ^ 71 := by norm_num
    linarith
  have hd2 : |value D.2.toBits| ≤ |F| * (1 / 2 ^ 17 + 1 / 2 ^ 50) + 1 / 2 ^ 19 := by
    have h1 : |value D.1.toBits| / 2 ^ 51 ≤ ((|F| + 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 51 :=
      div_le_div_of_nonneg_right hD1b (by norm_num)
    have h2 : (|value fl.toBits| + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) ≤
        (|F| / 2 ^ 17 + 1 / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have h3 : (|F| / 2 ^ 17 + 1 / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) +
        ((|F| + 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073) / 2 ^ 51 + 1 / 2 ^ 1073 =
        |F| * ((1 + 1 / 2 ^ 51) / 2 ^ 17 + (1 + 1 / 2 ^ 51) / 2 ^ 51) +
          ((1 / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) + (43 * (1 + 1 / 2 ^ 51) +
            1 / 2 ^ 1073) / 2 ^ 51 + 1 / 2 ^ 1073) := by ring
    have h4 : |F| * ((1 + 1 / 2 ^ 51) / 2 ^ 17 + (1 + 1 / 2 ^ 51) / 2 ^ 51) ≤
        |F| * (1 / 2 ^ 17 + 1 / 2 ^ 50) :=
      mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _)
    have h5 : (1 / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) + (43 * (1 + 1 / 2 ^ 51) +
        1 / 2 ^ 1073) / 2 ^ 51 + 1 / 2 ^ 1073 ≤ (1 : ℝ) / 2 ^ 19 := by norm_num
    linarith
  have hd1 : |value D.1.toBits| ≤ 2 ^ 899 := by
    linarith [(by norm_num : ((2 : ℝ) ^ 897 + 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 2 ^ 899)]
  have hLL : Real.log (Real.Gamma v) = -(lg + Real.log (a * s)) := hLr
  have hcore' : |-(lg + Real.log (a * s)) - (-value D.1.toBits + -value D.2.toBits)| ≤
      |lg - (F + value fl.toBits)| + ρ + 2 / 10 ^ 21 +
        (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
    rw [show -(lg + Real.log (a * s)) - (-value D.1.toBits + -value D.2.toBits) =
      -(lg + Real.log (a * s) - (value D.1.toBits + value D.2.toBits)) by ring, abs_neg]
    exact hcore
  unfold FastSpec
  dsimp only
  rw [hn1v, hn2v, hLL]
  simp only [abs_neg]
  refine ⟨hn1f, hn2f, he'f, ?_, ?_⟩
  · have : (1 : ℝ) / 2 ^ 1000 ≤ 4 * (448 / 10 ^ 22) / 2 := by norm_num
    have := mul_le_mul_of_nonneg_right hfh4 (by norm_num : (0 : ℝ) ≤ 448 / 10 ^ 22)
    linarith
  rcases hρ with hρ | ⟨hfar, hρ⟩
  · -- within `3/256` of an integer: the absolute form
    left
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith [(by norm_num : (2 : ℝ) ^ 899 + 2 ^ 49 * (2 ^ 897 / 2 ^ 62 + 1 / 2 ^ 78 +
        43 * (801 / 10 ^ 24) + (2 ^ 897 / 2 ^ 62 + 1 / 2 ^ 78 + 1 / 2 ^ 60) / 2 ^ 52) ≤ 2 ^ 1020)]
    · rw [hρ] at hcore'
      have h1 : (value eps.toBits + 1 / 2 ^ 60) / 2 ^ 52 ≤ |F| / 2 ^ 113 + 1 / 2 ^ 111 := by
        linarith
      linarith
  · -- the relative form
    right
    have hz0 : 0 ≤ 1 / 2 - |φ - 1 / 2| := by linarith
    have hsin := Real.mul_le_sin (x := Real.pi * (1 / 2 - |φ - 1 / 2|))
      (mul_nonneg Real.pi_pos.le hz0) (by
        have : 1 / 2 - |φ - 1 / 2| ≤ 1 / 2 := by linarith [abs_nonneg (φ - 1 / 2)]
        have := mul_le_mul_of_nonneg_left this Real.pi_pos.le
        linarith)
    rw [← mul_assoc, div_mul_cancel₀ 2 Real.pi_ne_zero, ← LgammaSinpi.sin_eq_near] at hsin
    have hs135 : 1 / 135 ≤ s := by
      rw [hsdef, le_div_iff₀ Real.pi_pos]
      have := Real.pi_lt_d2
      linarith
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs135
    have hs1 : s ≤ 1 := by
      rw [hsdef, div_le_one Real.pi_pos]
      linarith [Real.sin_le_one (Real.pi * φ), Real.pi_gt_three]
    have hρb : ρ ≤ 135 * (114 / 100 / 2 ^ 71) := by
      rw [hρ, div_le_iff₀ hs0]
      have := mul_le_mul_of_nonneg_left hs135 (by norm_num : (0 : ℝ) ≤ 135 * (114 / 100 / 2 ^ 71))
      linarith
    have ha6 : 6 ≤ a := by rw [hadef]; linarith
    have hlb := log_bounds
    have hlg64 : Real.log 64 ≤ lg :=
      lgamma_six.trans (GammaThresholds.lgamma_mono (by norm_num) ha6)
    have hla : Real.log 4 ≤ Real.log a := Real.log_le_log (by norm_num) (by linarith)
    have hls : -Real.log 135 ≤ Real.log s := by
      have := Real.log_le_log (by norm_num) hs135
      rw [one_div, Real.log_inv] at this
      exact this
    have has : Real.log (a * s) = Real.log a + Real.log s :=
      Real.log_mul (by linarith) hs0.ne'
    have hLp : 1 / 10 * lg ≤ lg + Real.log (a * s) := by rw [has]; linarith
    have hLp0 : 6 / 10 ≤ lg + Real.log (a * s) := by rw [has]; linarith
    have hla2 : Real.log a ≤ a := by linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < a)]
    have hls2 : Real.log s ≤ 0 := Real.log_nonpos hs0.le hs1
    have hFlg : |F| ≤ lg * (1 + 1 / 2 ^ 16) + 1 / 2 ^ 37 := by
      have h1 := abs_sub_abs_le_abs_sub (F + value fl.toBits) lg
      rw [abs_sub_comm] at h1
      have h2 := abs_sub_abs_le_abs_sub F (-value fl.toBits)
      rw [sub_neg_eq_add, abs_neg] at h2
      have hlgp : 0 ≤ lg := by linarith
      rw [abs_of_nonneg hlgp] at h1
      linarith
    have hlgu : lg ≤ 2 ^ 898 := by
      have h1 := abs_sub_abs_le_abs_sub lg (F + value fl.toBits)
      have h2 := abs_add_le F (value fl.toBits)
      have hlgp : 0 ≤ lg := by linarith
      rw [abs_of_nonneg hlgp] at h1
      linarith [(by norm_num : (2 : ℝ) ^ 897 + 2 ^ 897 / 2 ^ 17 + 1 / 2 ^ 38 +
        2 * (2 ^ 897 / 2 ^ 62 + 1 / 2 ^ 78) ≤ 2 ^ 898)]
    rw [abs_of_pos (by linarith : (0 : ℝ) < lg + Real.log (a * s))]
    refine ⟨by linarith [(by norm_num : (2 : ℝ) ^ 897 * (1 / 2 ^ 17 + 1 / 2 ^ 50) + 1 / 2 ^ 19 ≤
      2 ^ 1000)], by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 6 / 10)], by
      rw [has]; linarith [(by norm_num : (2 : ℝ) ^ 898 + 2 ^ 52 ≤ 2 ^ 1020)], ?_⟩
    have hd2' : (|value D.2.toBits| + value e'.toBits) / 2 ^ 52 ≤
        (|F| * (1 / 2 ^ 17 + 1 / 2 ^ 50) + 1 / 2 ^ 19 + (|F| / 2 ^ 62 + 1 / 2 ^ 78 +
          43 * (801 / 10 ^ 24) + (|F| / 2 ^ 62 + 1 / 2 ^ 78 + 1 / 2 ^ 60) / 2 ^ 52)) / 2 ^ 52 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith
    have hR : (lg + Real.log (a * s)) / 2 ^ 54 ≥ 1 / 10 * lg / 2 ^ 54 :=
      div_le_div_of_nonneg_right hLp (by norm_num)
    linarith

#print axioms eps8_value
#print axioms refl_tail

end Verified.Examples.LgammaReflTail
