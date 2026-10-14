import Verified.Examples.ErfcMainPath
import Verified.Examples.FmaSpecTheorem

/-!
The accuracy theorem for `Erfc.erfc`: for every finite binary64 input the result lies within one
representable step of the signed nearest-even rounding of `erfc x` (`erfc_within_one`).  The proof
follows the branches of `Erfc.erfcWith` on the bits `t` of `x`.  For `x ≤ -0x1.7744f8f74e94bp2`
the code returns `2 - 2^-54`, which rounds to 2, and `erfc x` lies within `2^-52` of 2
(`erfc_upper_neg`).  For `-0x1.c5bf891b4ef6ap-54 ≤ x ≤ -0` and `+0 ≤ x ≤ 0x1.c5bf891b4ef6ap-55` it
returns `fma (-x, 2^-54, 1)`, within half a spacing of `erfc x` (`tiny_erf`).  For
`x ≥ 0x1.b39dc41e48bfdp+4` it returns `2^-1074 · 0.25`, which rounds to 0, and `erfc x` lies below
`2^-1074` (`erfc_upper_big`).  The other finite inputs take the main path
(`ErfcMainPath.main_within`).  The fma's correctness (`FmaSpecTheorem.fma_nearest`) discharges
the hypothesis `FmaSpec.FmaNearest` of the main path.  The exceptional inputs give
`erfc (±0) = 1`, `erfc (+∞) = 0`, and `erfc (-∞) = 2`.
-/

namespace Verified.Examples.ErfcTheorem

open Real CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcRound ErfcTest ErfcSeries ErfcFastPath
  ErfcAsymZ ErfcAsymAccFin ErfcMainPath FmaSpec PolyBound PolyCalc RealErf F64NearestNonnegative

set_option exponentiation.threshold 4096

/-- `exp (-n)` below `(10^10 / 27182818283)^n`. -/
theorem exp_neg_nat_le (n : ℕ) : exp (-(n : ℝ)) ≤ ((10 ^ 10 / 27182818283 : ℚ) : ℝ) ^ n := by
  have h1 : ((27182818283 / 10 ^ 10 : ℚ) : ℝ) < exp 1 := by
    have := Real.exp_one_gt_d9; push_cast; linarith
  have hpos : (0 : ℝ) < ((27182818283 / 10 ^ 10 : ℚ) : ℝ) := by push_cast; norm_num
  rw [show -(n : ℝ) = n * (-1) by ring, Real.exp_nat_mul, Real.exp_neg]
  apply pow_le_pow_left₀ (by positivity)
  rw [show ((10 ^ 10 / 27182818283 : ℚ) : ℝ) = (((27182818283 / 10 ^ 10 : ℚ) : ℝ))⁻¹ by
    push_cast; ring]
  exact inv_anti₀ hpos h1.le

/-- `erfc z ≤ exp (-n) · 0.57 / z` for `z ≥ 2` and `n ≤ z²`. -/
theorem erfc_le_exp (z : ℝ) (h2 : 2 ≤ z) (n : ℕ) (hn : (n : ℝ) ≤ z ^ 2) :
    erfc z ≤ ((10 ^ 10 / 27182818283 : ℚ) : ℝ) ^ n * (57 / 100) / z := by
  have hG := G_bounds z h2
  have hz0 : 0 < z := by linarith
  have hE : exp (-z ^ 2) ≤ ((10 ^ 10 / 27182818283 : ℚ) : ℝ) ^ n :=
    (exp_le_exp.mpr (by linarith)).trans (exp_neg_nat_le n)
  have hx : erfcx z ≤ 57 / 100 / z := by
    rw [le_div_iff₀ hz0]; nlinarith [hG.2]
  rw [erfc_eq, mul_div_assoc]
  exact mul_le_mul hE hx (erfcx_pos z).le (by positivity)

/-- `erfc z < 2^-52` for `z ≥ 0x1.7744f8f74e94bp2`. -/
theorem erfc_upper_neg (z : ℝ) (hz : (ratOfWord 0x4017744F8F74E94B : ℝ) ≤ z) :
    erfc z < 1 / 2 ^ 52 := by
  have k : (5863 / 1000 : ℚ) ≤ ratOfWord 0x4017744F8F74E94B ∧
      (10 ^ 10 / 27182818283 : ℚ) ^ 34 * (57 / 100) / (5863 / 1000) < 1 / 2 ^ 52 := by
    decide +kernel
  have hz1 : (5863 / 1000 : ℝ) ≤ z := le_trans (by qc k.1) hz
  have h := erfc_le_exp z (by linarith) 34 (by push_cast; nlinarith)
  have h2 : ((10 ^ 10 / 27182818283 : ℚ) : ℝ) ^ 34 * (57 / 100) / z ≤
      ((10 ^ 10 / 27182818283 : ℚ) : ℝ) ^ 34 * (57 / 100) / (5863 / 1000) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hz1
  have h3 : (((10 ^ 10 / 27182818283 : ℚ) ^ 34 * (57 / 100) / (5863 / 1000) : ℚ) : ℝ) <
      ((1 / 2 ^ 52 : ℚ) : ℝ) := by qc k.2
  push_cast at h3 ⊢
  linarith

/-- `erfc z < 2^-1074` for `z ≥ 0x1.b39dc41e48bfdp+4`. -/
theorem erfc_upper_big (z : ℝ) (hz : (ratOfWord 0x403B39DC41E48BFD : ℝ) ≤ z) :
    erfc z < 1 / 2 ^ 1074 := by
  have k : (27226 / 1000 : ℚ) ≤ ratOfWord 0x403B39DC41E48BFD ∧
      (10 ^ 10 / 27182818283 : ℚ) ^ 741 * (57 / 100) / (27226 / 1000) < 1 / 2 ^ 1074 := by
    decide +kernel
  have hz1 : (27226 / 1000 : ℝ) ≤ z := le_trans (by qc k.1) hz
  have h := erfc_le_exp z (by linarith) 741 (by push_cast; nlinarith)
  have h2 : ((10 ^ 10 / 27182818283 : ℚ) : ℝ) ^ 741 * (57 / 100) / z ≤
      ((10 ^ 10 / 27182818283 : ℚ) : ℝ) ^ 741 * (57 / 100) / (27226 / 1000) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hz1
  have h3 : (((10 ^ 10 / 27182818283 : ℚ) ^ 741 * (57 / 100) / (27226 / 1000) : ℚ) : ℝ) <
      ((1 / 2 ^ 1074 : ℚ) : ℝ) := by qc k.2
  push_cast at h3 ⊢
  linarith

/-- `erf z` for `0 ≤ z ≤ T` is at most the series bound at `T` with one term. -/
theorem tiny_erf (z : ℝ) (T : ℚ) (h0 : 0 ≤ z) (hT : z ≤ T) :
    erf z ≤ ((sHi * evalQ (ser 1) T + sHi * serRem 1 T : ℚ) : ℝ) := by
  have hT0 : (0 : ℝ) ≤ T := h0.trans hT
  have hS : 0 ≤ evalQ (ser 1) T := by
    have : evalQ (ser 1) T = T := by
      simp [ser, PolyCalculus.oddP, PolyCalculus.spread, erfCoeffs, evalQ]
    rw [this]; exact_mod_cast hT0
  exact (erf_strictMono.monotone hT).trans
    (ErfcHardBase.erf_encl 1 T (by exact_mod_cast hT0) hS).2

/-- A word below `limit` is finite. -/
theorem finite_of_lt (v : UInt64) (hv : v.toNat < limit) : Finite v := by
  have hl : limit = 0x7FF0000000000000 := rfl
  rw [hl] at hv
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne, ne_eq]
  omega

/-- A positive finite float is a word below `limit`. -/
theorem lt_limit_of_pos (c : Float) (hc : ff c) (hpos : 0 < fv c) : c.toBits.toNat < limit := by
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude c.toBits := by
    by_contra h0
    push Not at h0
    have hz : Wasm.IEEE64.scaledMagnitude c.toBits = 0 := by omega
    have : fv c = 0 := by
      simp only [fv, value, Wasm.IEEE64.scaledValue, hz]
      split <;> simp
    linarith
  have hsign : Wasm.IEEE64.sign c.toBits = false := by
    rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign c.toBits) with h | h
    · have := (F64Magnitude.sign_value c.toBits hmag).mp h
      exact absurd this (not_lt.mpr hpos.le)
    · exact h
  exact F64Magnitude.lt_limit_of_finite c.toBits hc hsign

/-- The fma's result is a nearest word of `a b + c` when that lies in `(1/2, 3/2)`. -/
theorem nearest_of_fma (hF : FmaNearest) (a b c : Float) (ha : ff a) (hb : ff b) (hc : ff c)
    (hs1 : 1 / 2 < fv a * fv b + fv c) (hs2 : fv a * fv b + fv c < 3 / 2) :
    Nearest (fv a * fv b + fv c) (Fma.fma a b c).toBits := by
  obtain ⟨rf, rn⟩ := hF a b c ha hb hc (by
    change |fv a * fv b + fv c| ≤ 2 ^ 1023
    rw [abs_le]; constructor <;> linarith [show (3 / 2 : ℝ) ≤ 2 ^ 1023 by norm_num])
  obtain ⟨of, ov⟩ := one_val
  have h1 := rn _ of
  change |fv (Fma.fma a b c) - (fv a * fv b + fv c)| ≤ |fv 1.0 - (fv a * fv b + fv c)| at h1
  rw [ov] at h1
  have k2 : |1 - (fv a * fv b + fv c)| < fv a * fv b + fv c := by
    rw [abs_lt]; constructor <;> linarith
  have hpos : 0 < fv (Fma.fma a b c) := by
    linarith [neg_abs_le (fv (Fma.fma a b c) - (fv a * fv b + fv c))]
  exact ⟨lt_limit_of_pos _ rf hpos, fun v hv => rn v (finite_of_lt v hv)⟩

/-- One step for a word `w` of value within one spacing of `y`, two spacings into binade `e`. -/
theorem word_within (y : ℝ) (w : UInt64) (hw : w.toNat < limit) (e : ℕ) (he : 1 ≤ e)
    (he' : e ≤ 2046) (hy : ((2 : ℝ) ^ (e + 51) + 2 * 2 ^ (e - 1)) / 2 ^ 1074 ≤ y)
    (hyt : y < 2 ^ 1023) (hd : |value w - y| < (2 : ℝ) ^ (e - 1) / 2 ^ 1074) :
    F64SignedRounding.WithinSteps 1 y w :=
  F64NearestSteps.within_of_interior y (value w) w e he he' hy
    (F64NearestSteps.below_threshold y hyt)
    ⟨hw, fun v _ => by rw [sub_self, abs_zero]; exact abs_nonneg _⟩ hd

/-- A magnitude test on the bits of `x`. -/
theorem mag_le (x : Float) (W : UInt64) (hW : W.toNat < 2 ^ 63) :
    W.toNat ≤ x.toBits.toNat % 2 ^ 63 ↔ value W ≤ |fv x| := by
  unfold fv
  rw [← F64UpperWord.value_abs, F64PositiveOrder.value_le_iff hW
    (by rw [F64UpperWord.abs_toNat]; omega), F64UpperWord.abs_toNat]

theorem and_mask (t : UInt64) : (t &&& 0x7FFFFFFFFFFFFFFF).toNat = t.toNat % 2 ^ 63 := by
  rw [UInt64.toNat_and, show (0x7FFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem finite_mag (x : Float) (hx : ff x) : x.toBits.toNat % 2 ^ 63 < 0x7FF0000000000000 := by
  have h := F64UpperWord.finite_high _ hx
  rw [F64UpperWord.high_toNat] at h
  omega

/-- The words of the special ranges. -/
theorem range_words :
    ratOfWord 0xBC9C5BF891B4EF6A = -ratOfWord 0x3C9C5BF891B4EF6A ∧
    Finite (0xBC9C5BF891B4EF6A : UInt64) ∧ Finite (0x3C8C5BF891B4EF6A : UInt64) ∧
    Finite (0x3C90000000000000 : UInt64) ∧ ratOfWord 0x3C90000000000000 = 1 / 2 ^ 54 ∧
    ratOfWord 0x3C9C5BF891B4EF6A / 2 ^ 54 +
      (sHi * evalQ (ser 1) (ratOfWord 0x3C9C5BF891B4EF6A) +
        sHi * serRem 1 (ratOfWord 0x3C9C5BF891B4EF6A)) < 1 / 2 ^ 53 ∧
    ratOfWord 0x3C8C5BF891B4EF6A / 2 ^ 54 +
      (sHi * evalQ (ser 1) (ratOfWord 0x3C8C5BF891B4EF6A) +
        sHi * serRem 1 (ratOfWord 0x3C8C5BF891B4EF6A)) < 1 / 2 ^ 53 ∧
    0 ≤ ratOfWord 0x3C9C5BF891B4EF6A ∧ 0 ≤ ratOfWord 0x3C8C5BF891B4EF6A ∧
    ratOfWord 0x3C9C5BF891B4EF6A < 1 / 4 ∧ ratOfWord 0x3C8C5BF891B4EF6A < 1 / 4 ∧
    -(47 / 8 : ℚ) < -ratOfWord 0x4017744F8F74E94B ∧ 0 < ratOfWord 0x403B39DC41E48BFD ∧
    (0x4017744F8F74E94B : UInt64).toNat < 2 ^ 63 ∧ (0x403B39DC41E48BFD : UInt64).toNat < 2 ^ 63 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

/-- One step for every finite `x`, given `FmaSpec.FmaNearest`. -/
theorem erfcWith_within (hF : FmaNearest) (x : Float) (hx : ff x) :
    F64SignedRounding.WithinSteps 1 (erfc (fv x))
      (Erfc.erfcWith Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable Erfc.asymAccTable
        Erfc.expAccTable Erfc.excTable x).toBits := by
  obtain ⟨wn, fn, fp, fc, vc, bn, bp, n0, p0, n1, p1, w47, wbig, wl1, wl2⟩ := range_words
  obtain ⟨nf, nv⟩ := neg_f x hx
  obtain ⟨cf, cv⟩ := ofBits_ff _ fc
  obtain ⟨of, ov⟩ := one_val
  have hfm := finite_mag x hx
  have hu54 : fv (Float.ofBits 0x3C90000000000000) = 1 / 2 ^ 54 := by rw [cv, vc]; push_cast; ring
  unfold Erfc.erfcWith
  dsimp only
  split
  · -- the sign bit is set
    rename_i hs
    have hs' : 2 ^ 63 ≤ x.toBits.toNat := by
      have := UInt64.le_iff_toNat_le.mp hs; simpa using this
    have hneg : fv x ≤ 0 := value_nonpos_of_ge _ hs'
    have habs : |fv x| = -fv x := abs_of_nonpos hneg
    split
    · rename_i h1
      have h1' : (0xC017744F8F74E94B : UInt64).toNat ≤ x.toBits.toNat :=
        UInt64.le_iff_toNat_le.mp h1
      split
      · rename_i h2
        have := UInt64.le_iff_toNat_le.mp h2
        exfalso
        have : (0xFFF0000000000000 : UInt64).toNat = 0xFFF0000000000000 := rfl
        have := x.toBits.toNat_lt
        omega
      · -- `x ≤ -0x1.7744f8f74e94bp2`: the result 2
        have hm : (0x4017744F8F74E94B : UInt64).toNat ≤ x.toBits.toNat % 2 ^ 63 := by
          have : (0xC017744F8F74E94B : UInt64).toNat = 0x4017744F8F74E94B + 2 ^ 63 := rfl
          have h2 : (0x4017744F8F74E94B : UInt64).toNat = 0x4017744F8F74E94B := rfl
          have := x.toBits.toNat_lt
          omega
        have hz := (mag_le x _ wl1).mp hm
        rw [habs, ← ratOfWord_cast] at hz
        have hup := erfc_upper_neg (-fv x) hz
        have hy : erfc (fv x) = 2 - erfc (-fv x) := by
          rw [show fv x = -(-fv x) by ring, erfc_neg, neg_neg]
        have hw : (2.0 - Float.ofBits 0x3C90000000000000).toBits = 0x4000000000000000 := by
          rw [F64Bits.toBits_sub, F64Bits.toBits_ofBits,
            show (2.0 : Float).toBits = 0x4000000000000000 from rfl]
          decide +kernel
        have hv2 : value (0x4000000000000000 : UInt64) = 2 := by
          rw [← ratOfWord_cast, show ratOfWord 0x4000000000000000 = 2 by decide +kernel]
          norm_num
        rw [hw, hy]
        have hp := erfc_pos (-fv x)
        refine word_within _ _ (by decide) 1023 (by norm_num) (by norm_num) ?_ ?_ ?_
        · norm_num; linarith
        · linarith [show (2 : ℝ) < 2 ^ 1023 by norm_num]
        · rw [hv2, show (2 : ℝ) - (2 - erfc (-fv x)) = erfc (-fv x) by ring, abs_of_pos hp]
          norm_num; linarith
    · rename_i h1
      have h1' : x.toBits.toNat < (0xC017744F8F74E94B : UInt64).toNat := by
        have := UInt64.le_iff_toNat_le.not.mp h1; omega
      have hm : ¬ (0x4017744F8F74E94B : UInt64).toNat ≤ x.toBits.toNat % 2 ^ 63 := by
        have : (0xC017744F8F74E94B : UInt64).toNat = 0x4017744F8F74E94B + 2 ^ 63 := rfl
        have h2 : (0x4017744F8F74E94B : UInt64).toNat = 0x4017744F8F74E94B := rfl
        omega
      have hz : -fv x < ratOfWord 0x4017744F8F74E94B := by
        have := (mag_le x _ wl1).not.mp hm
        rw [habs, ← ratOfWord_cast] at this; linarith
      have hlo : -(47 / 8) < fv x := by
        have : ((-(47 / 8) : ℚ) : ℝ) < ((-ratOfWord 0x4017744F8F74E94B : ℚ) : ℝ) := by qc w47
        push_cast at this; linarith
      obtain ⟨tf, tv⟩ := ofBits_ff _ fn
      split
      · -- `-0x1.c5bf891b4ef6ap-54 ≤ x ≤ -0`
        rename_i h2
        have hT : -(ratOfWord 0x3C9C5BF891B4EF6A : ℝ) ≤ fv x := by
          have := (fle_iff _ _ tf hx).mp h2
          rw [tv, wn] at this; push_cast at this; exact this
        have herf := tiny_erf (-fv x) _ (by linarith) (by linarith)
        have herf0 := erf_nonneg (-fv x) (by linarith)
        have hy : erfc (fv x) = 1 + erf (-fv x) := by
          unfold erfc; rw [erf_neg]; ring
        have k1 : ((ratOfWord 0x3C9C5BF891B4EF6A / 2 ^ 54 +
            (sHi * evalQ (ser 1) (ratOfWord 0x3C9C5BF891B4EF6A) +
              sHi * serRem 1 (ratOfWord 0x3C9C5BF891B4EF6A)) : ℚ) : ℝ) < ((1 / 2 ^ 53 : ℚ) : ℝ) := by
          qc bn
        have k2 : ((ratOfWord 0x3C9C5BF891B4EF6A : ℚ) : ℝ) < ((1 / 4 : ℚ) : ℝ) := by qc n1
        push_cast at k1 k2 herf
        have hs : fv (-x) * fv (Float.ofBits 0x3C90000000000000) + fv 1.0 = 1 - fv x / 2 ^ 54 := by
          rw [nv, hu54, ov]; ring
        have hc := nearest_of_fma hF (-x) (Float.ofBits 0x3C90000000000000) 1.0 nf cf of
          (by rw [hs]; nlinarith) (by rw [hs]; nlinarith)
        rw [hs] at hc
        rw [hy]
        refine F64NearestSteps.within_of_half _ _ _ 1023 (by norm_num) (by norm_num) (by norm_num; linarith)
          (F64NearestSteps.below_threshold _ (by linarith [show (2 : ℝ) < 2 ^ 1023 by norm_num])) hc ?_
        rw [abs_lt]; norm_num; constructor <;> nlinarith
      · -- the main path
        rename_i h2
        have hT : fv x < -(ratOfWord 0x3C9C5BF891B4EF6A : ℝ) := by
          by_contra hc
          exact h2 ((fle_iff _ _ tf hx).mpr (by rw [tv, wn]; push_cast; linarith))
        have k0 : ((0 : ℚ) : ℝ) ≤ ((ratOfWord 0x3C9C5BF891B4EF6A : ℚ) : ℝ) := by qc n0
        have kb : ((0 : ℚ) : ℝ) < ((ratOfWord 0x403B39DC41E48BFD : ℚ) : ℝ) := by qc wbig
        push_cast at k0 kb
        exact main_within hF x hx hlo (by linarith) (by linarith)
  · -- the sign bit is clear
    rename_i hs
    have hs' : x.toBits.toNat < 2 ^ 63 := by
      have := UInt64.le_iff_toNat_le.not.mp hs; simp at this; omega
    have hpos : 0 ≤ fv x := by
      have := (F64PositiveOrder.value_le_iff (left := 0) (by decide) hs').mpr (Nat.zero_le _)
      rwa [F64Magnitude.value_zero] at this
    have habs : |fv x| = fv x := abs_of_nonneg hpos
    have herf0 := erf_nonneg (fv x) hpos
    split
    · rename_i h1
      have h1' := UInt64.le_iff_toNat_le.mp h1
      rw [and_mask] at h1'
      split
      · rename_i h2
        have := UInt64.le_iff_toNat_le.mp h2
        rw [and_mask] at this
        exfalso
        have : (0x7FF0000000000000 : UInt64).toNat = 0x7FF0000000000000 := rfl
        omega
      · -- `x ≥ 0x1.b39dc41e48bfdp+4`: the result 0
        have hz := (mag_le x _ wl2).mp h1'
        rw [habs, ← ratOfWord_cast] at hz
        have hup := erfc_upper_big (fv x) hz
        have hw : (Float.ofBits 0x0000000000000001 * 0.25).toBits = 0 := by
          rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits,
            show (0.25 : Float).toBits = 0x3FD0000000000000 from rfl]
          decide +kernel
        rw [hw]
        have hp := erfc_pos (fv x)
        refine within_small 0 (by unfold CodeLib.IEEE64.Finite; decide) (by
          rw [F64Magnitude.value_zero]) _ hp.le (by unfold erfc; linarith) ?_
        rw [F64Magnitude.value_zero, zero_sub, abs_neg, abs_of_pos hp]
        exact hup
    · rename_i h1
      have h1' : ¬ (0x403B39DC41E48BFD : UInt64).toNat ≤ x.toBits.toNat % 2 ^ 63 := by
        have := UInt64.le_iff_toNat_le.not.mp h1
        rwa [and_mask] at this
      have hhi : fv x < ratOfWord 0x403B39DC41E48BFD := by
        have := (mag_le x _ wl2).not.mp h1'
        rw [habs, ← ratOfWord_cast] at this; linarith
      obtain ⟨tf, tv⟩ := ofBits_ff _ fp
      split
      · -- `+0 ≤ x ≤ 0x1.c5bf891b4ef6ap-55`
        rename_i h2
        have hT : fv x ≤ ratOfWord 0x3C8C5BF891B4EF6A := by
          have := (fle_iff _ _ hx tf).mp h2
          rwa [tv] at this
        have herf := tiny_erf (fv x) _ hpos hT
        have k1 : ((ratOfWord 0x3C8C5BF891B4EF6A / 2 ^ 54 +
            (sHi * evalQ (ser 1) (ratOfWord 0x3C8C5BF891B4EF6A) +
              sHi * serRem 1 (ratOfWord 0x3C8C5BF891B4EF6A)) : ℚ) : ℝ) < ((1 / 2 ^ 53 : ℚ) : ℝ) := by
          qc bp
        have k2 : ((ratOfWord 0x3C8C5BF891B4EF6A : ℚ) : ℝ) < ((1 / 4 : ℚ) : ℝ) := by qc p1
        push_cast at k1 k2 herf
        have hs : fv (-x) * fv (Float.ofBits 0x3C90000000000000) + fv 1.0 = 1 - fv x / 2 ^ 54 := by
          rw [nv, hu54, ov]; ring
        have hc := nearest_of_fma hF (-x) (Float.ofBits 0x3C90000000000000) 1.0 nf cf of
          (by rw [hs]; nlinarith) (by rw [hs]; nlinarith)
        rw [hs] at hc
        have hy : erfc (fv x) = 1 - erf (fv x) := rfl
        rw [hy]
        refine F64NearestSteps.within_of_interior _ _ _ 1022 (by norm_num) (by norm_num)
          (by norm_num; nlinarith)
          (F64NearestSteps.below_threshold _ (by linarith [show (2 : ℝ) < 2 ^ 1023 by norm_num])) hc ?_
        rw [abs_lt]; norm_num; constructor <;> nlinarith
      · -- the main path
        rename_i h2
        have hT : (ratOfWord 0x3C8C5BF891B4EF6A : ℝ) < fv x := by
          by_contra hc
          exact h2 ((fle_iff _ _ hx tf).mpr (by rw [tv]; linarith))
        have k0 : ((0 : ℚ) : ℝ) ≤ ((ratOfWord 0x3C8C5BF891B4EF6A : ℚ) : ℝ) := by qc p0
        push_cast at k0
        exact main_within hF x hx (by linarith) (by linarith) hhi

/-- One step for `Erfc.erfc x` for every finite `x`. -/
theorem erfc_within_one (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (RealErf.erfc (value x.toBits)) (Erfc.erfc x).toBits :=
  erfcWith_within FmaSpecTheorem.fma_nearest x hxf

#print axioms erfc_within_one

end Verified.Examples.ErfcTheorem
