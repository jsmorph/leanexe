import Verified.Examples.AsinhTheoremBranches
import Verified.Examples.LogTheorem
import Verified.Examples.Log1pTheoremConst
import LeanExe.ProofKit.F64Compose
import Verified.Examples.AtanTwoErr
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
`log a + ln2` for `a ≥ 2 ^ 28`, the large branches of `Asinh.asinh` and `Asinh.acosh`.  `Log.log a`
lies within one step of `log a`, so within one and a half spacings of the binade of `log a`, or two
and a half in its top two spacings (`F64Compose.error_of_within`).  The sum with `ln2` rounds to a
nearest word, and its exact value lies within two spacings of `log a + log 2`, of the binade of
`log a` or, near its top, of the next one, where the sum and the target lie.  `arsinh a` and
`arcosh a` differ from `log a + log 2` by at most `1/a²`.
-/

namespace Verified.Examples.AsinhTheoremLarge
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound AtanTheoremBranches AsinhTheoremBranches

set_option exponentiation.threshold 4096

/-- A word within one step of `y` and close to it is finite. -/
theorem finite_of_close (y E : ℝ) (w : UInt64) (h : F64SignedRounding.WithinSteps 1 y w)
    (hE : |value w - y| ≤ E) (hy : |y| + E < 2 ^ 1024) : Finite w := by
  have hw := w.toNat_lt
  have hn := h.1
  by_contra hnf
  have he : w.toNat / 2 ^ 52 % 2 ^ 11 = 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
      ne_eq, not_not] at hnf
    exact hnf
  have hm : Wasm.IEEE64.scaledMagnitude w = 2 ^ 2098 := by
    have hf : w.toNat % 2 ^ 52 = 0 := by omega
    simp only [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, he, hf]
    norm_num
  have ha := F64RoundNearest.abs_value w
  have h2 : ((2 ^ 2098 : ℕ) : ℝ) / 2 ^ 1074 = 2 ^ 1024 := by norm_num
  rw [hm, h2] at ha
  have h3 := abs_sub_abs_le_abs_sub (value w) y
  linarith

theorem ln2_word : value ln2F.toBits = 6243314768165359 / 2 ^ 53 := by
  rw [ln2F, F64Bits.toBits_ofBits, ite_eq_right (by decide),
    AtanTheoremCases.word_eq 0x3FE62E42FEFA39EF (6243314768165359 / 2 ^ 53) (by decide +kernel)]
  norm_num

theorem ln2_finite : Finite ln2F.toBits := by
  rw [ln2F, F64Bits.toBits_ofBits]
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem ln2_word_close : |value ln2F.toBits - Real.log 2| ≤ 1 / 2 ^ 55 := by
  have h := Log1pTheoremConst.ln2_close
  rw [← PolyBound.ratOfWord_cast 0x3FE62E42FEE00000,
    ← PolyBound.ratOfWord_cast 0x3DEA39EF35793C76] at h
  rw [ln2_word]
  have hq : -(1 / 2 ^ 55 - 1 / 2 ^ 81 : ℚ) ≤ 6243314768165359 / 2 ^ 53 -
        (ratOfWord 0x3FE62E42FEE00000 + ratOfWord 0x3DEA39EF35793C76) ∧
      6243314768165359 / 2 ^ 53 - (ratOfWord 0x3FE62E42FEE00000 +
        ratOfWord 0x3DEA39EF35793C76) ≤ (1 / 2 ^ 55 - 1 / 2 ^ 81 : ℚ) := by
    decide +kernel
  have h1 := (Rat.cast_le (K := ℝ)).mpr hq.1
  have h2 := (Rat.cast_le (K := ℝ)).mpr hq.2
  push_cast at h1 h2
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- `Log.log a + ln2` within two steps of a target `Y` that lies within `2 ^ -56` of
`log a + log 2`, for `a ≥ 2 ^ 28`. -/
theorem log_ln2 (a : Float) (ha : Finite a.toBits) (ha0 : 2 ^ 28 ≤ value a.toBits) (Y : ℝ)
    (hY : |Y - (Real.log (value a.toBits) + Real.log 2)| ≤ 1 / 2 ^ 56) :
    F64SignedRounding.WithinSteps 2 Y (Log.log a + ln2F).toBits := by
  have hva0 : 0 < value a.toBits := lt_of_lt_of_le (by positivity) ha0
  have hlc := LogTheorem.log_within_one a ha hva0
  set L := Real.log (value a.toBits) with hL
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hL16 : 16 ≤ L := by
    have h1 : Real.log (2 ^ 28) ≤ L := Real.log_le_log (by positivity) ha0
    rw [Real.log_pow] at h1
    push_cast at h1
    norm_num at hl2a
    linarith
  have hL710 : L < 710 := by
    have hfe : Wasm.IEEE64.exponent a.toBits < 2047 := by
      have h := ha
      simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
      have := a.toBits.toNat_lt
      simp only [Wasm.IEEE64.exponent] at h ⊢
      omega
    have hvb := F64Magnitude.magnitude_lt a.toBits 2047 1024 (by norm_num) (by norm_num) hfe
    rw [abs_of_pos hva0] at hvb
    have h1 : L < Real.log (2 ^ (1024 : ℤ)) := Real.log_lt_log hva0 hvb
    rw [Real.log_zpow] at h1
    push_cast at h1
    norm_num at hl2b
    linarith
  obtain ⟨n, hn2, hn, hBn, hBn2⟩ := F64RoundNearest.binade_of_real L
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1021 ≤ 16)])
    (by linarith [(by norm_num : (710 : ℝ) < 2 ^ 1022)])
  rw [F64PositiveSpacing.boundary_value n (by omega) (by omega)] at hBn hBn2
  have hn_hi : n ≤ 1032 := by
    by_contra hc
    have h1 : (2 : ℝ) ^ (1033 + 51) / 2 ^ 1074 ≤ 2 ^ (n + 51) / 2 ^ 1074 :=
      div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    norm_num at h1
    linarith
  have hn_lo : 1027 ≤ n := by
    by_contra hc
    have h1 : (2 : ℝ) ^ (n + 51) / 2 ^ 1074 ≤ 2 ^ (1026 + 51) / 2 ^ 1074 :=
      div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    norm_num at h1
    linarith
  set sp := (2 : ℝ) ^ (n - 1) / 2 ^ 1074 with hsp
  set B := (2 : ℝ) ^ (n + 51) / 2 ^ 1074 with hB
  have hsp_hi : sp ≤ 1 / 2 ^ 43 := by
    have h1 : (2 : ℝ) ^ (n - 1) ≤ 2 ^ 1031 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : sp ≤ (2 : ℝ) ^ 1031 / 2 ^ 1074 := div_le_div_of_nonneg_right h1 (by positivity)
    norm_num at h2 ⊢
    linarith
  have hsp_lo : 1 / 2 ^ 48 ≤ sp := by
    have h1 : (2 : ℝ) ^ 1026 ≤ 2 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ 1026 / 2 ^ 1074 ≤ sp := div_le_div_of_nonneg_right h1 (by positivity)
    norm_num at h2 ⊢
    linarith
  have hBsp : B = 2 ^ 52 * sp := by
    rw [hB, hsp, show n + 51 = (n - 1) + 52 by omega, pow_add]
    ring
  obtain ⟨e25, e15⟩ := F64Compose.error_of_within L _ hlc n hn2 (by omega) hBn hBn2
  have e25' := abs_le.mp e25
  have hlf : Finite (Log.log a).toBits := finite_of_close L _ _ hlc e25 (by
    rw [abs_of_pos (by linarith)]
    linarith [(by norm_num : (710 : ℝ) + 1 < 2 ^ 1024)])
  have hl2 := abs_le.mp ln2_word_close
  have hlw := ln2_word
  have hY' := abs_le.mp hY
  set S := value (Log.log a).toBits + value ln2F.toBits with hS
  have hS1 : B ≤ S := by
    have hlw := ln2_word
    linarith
  have hRd := F64RoundNearest.add_rounded (Log.log a).toBits ln2F.toBits hlf ln2_finite
    (ne_of_gt (by linarith [(by positivity : (0 : ℝ) < B)]))
    (by
      rw [abs_of_pos (by linarith [(by positivity : (0 : ℝ) < B)])]
      have hlw := ln2_word
      linarith [(by norm_num : (712 : ℝ) < 2 ^ 1023)])
  rw [← F64Bits.toBits_add] at hRd
  have hYt : |Y| < 2 ^ 1023 := by
    rw [abs_lt]
    constructor <;> linarith [(by norm_num : (712 : ℝ) < 2 ^ 1023)]
  by_cases htop : L + 2 * sp ≤ 2 * B
  · have he := abs_le.mp (e15 htop)
    refine F64TwoSteps.within_two_of_rounded _ S Y hRd n (by omega) (by omega) ?_ ?_ ?_ hYt
    · rw [F64PositiveSpacing.boundary_value n (by omega) (by omega), abs_of_pos (by
        linarith [(by positivity : (0 : ℝ) < B)])]
      exact hS1
    · rw [F64PositiveSpacing.boundary_value n (by omega) (by omega), abs_of_pos (by
        linarith [(by positivity : (0 : ℝ) < B)])]
      linarith
    · rw [abs_lt]
      constructor <;> linarith
  · push Not at htop
    refine F64TwoSteps.within_two_of_rounded _ S Y hRd (n + 1) (by omega) (by omega) ?_ ?_ ?_ hYt
    · rw [F64PositiveSpacing.boundary_value (n + 1) (by omega) (by omega),
        show n + 1 + 51 = (n + 51) + 1 by omega, pow_succ, abs_of_pos (by
        linarith [(by positivity : (0 : ℝ) < B)])]
      have h2B : (2 : ℝ) ^ (n + 51) * 2 / 2 ^ 1074 = 2 * B := by rw [hB]; ring
      rw [h2B]
      linarith
    · rw [F64PositiveSpacing.boundary_value (n + 1) (by omega) (by omega),
        show n + 1 + 51 = (n + 51) + 1 by omega, pow_succ, abs_of_pos (by
        linarith [(by positivity : (0 : ℝ) < B)])]
      have h2B : (2 : ℝ) ^ (n + 51) * 2 / 2 ^ 1074 = 2 * B := by rw [hB]; ring
      rw [h2B]
      linarith
    · have h4 : (2 : ℝ) * ((2 : ℝ) ^ (n + 1 - 1) / 2 ^ 1074) = 4 * sp := by
        rw [hsp, show n + 1 - 1 = (n - 1) + 1 by omega,
          show (2 : ℝ) ^ ((n - 1) + 1) = 2 ^ (n - 1) * 2 from pow_succ 2 (n - 1)]
        ring
      rw [h4, abs_lt]
      constructor <;> linarith


theorem arsinh_large (a : ℝ) (ha : 2 ^ 28 ≤ a) :
    |Real.arsinh a - (Real.log a + Real.log 2)| ≤ 1 / 2 ^ 56 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  set s := Real.sqrt (1 + a ^ 2) with hs
  have hs1 : a ≤ s := (Real.le_sqrt ha0.le (by positivity)).mpr (by nlinarith)
  have hs2 : s ≤ a + 1 / (2 * a) := by
    rw [hs, Real.sqrt_le_left (by positivity)]
    have h3 : (a + 1 / (2 * a)) ^ 2 = a ^ 2 + 1 + 1 / (4 * a ^ 2) := by field_simp; ring
    rw [h3]
    have : 0 ≤ 1 / (4 * a ^ 2) := by positivity
    linarith
  have hpos : 0 < (a + s) / (2 * a) := by positivity
  have hr1 : 1 ≤ (a + s) / (2 * a) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hr2 : (a + s) / (2 * a) ≤ 1 + 1 / (4 * a ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : (1 + 1 / (4 * a ^ 2)) * (2 * a) = 2 * a + 1 / (2 * a) := by field_simp; ring
    rw [h3]
    linarith
  have hlog : Real.arsinh a - (Real.log a + Real.log 2) = Real.log ((a + s) / (2 * a)) := by
    rw [Real.arsinh, ← hs, Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num)
      ha0.ne']
    ring
  rw [hlog, abs_of_nonneg (Real.log_nonneg hr1)]
  have h3 := Real.log_le_sub_one_of_pos hpos
  have h4 : 1 / (4 * a ^ 2) ≤ 1 / 2 ^ 56 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

theorem arcosh_large (a : ℝ) (ha : 2 ^ 28 ≤ a) :
    |Real.arcosh a - (Real.log a + Real.log 2)| ≤ 1 / 2 ^ 56 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have ha1 : 1 ≤ a := le_trans (by norm_num) ha
  set s := Real.sqrt (a ^ 2 - 1) with hs
  have hs1 : a - 1 / a ≤ s := by
    have h3 : 0 ≤ a - 1 / a := by
      rw [sub_nonneg, div_le_iff₀ ha0]
      nlinarith
    rw [hs]
    apply (Real.le_sqrt h3 (by nlinarith)).mpr
    have h4 : (a - 1 / a) ^ 2 = a ^ 2 - 2 + 1 / a ^ 2 := by field_simp; ring
    rw [h4]
    have h5 : 1 / a ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  have hs2 : s ≤ a := by
    rw [hs, Real.sqrt_le_left ha0.le]
    linarith
  have hpos : 0 < (a + s) / (2 * a) := by
    apply div_pos _ (by positivity)
    have : 0 ≤ s := Real.sqrt_nonneg _
    linarith
  have hr1 : (a + s) / (2 * a) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hr2 : 1 - 1 / (2 * a ^ 2) ≤ (a + s) / (2 * a) := by
    rw [le_div_iff₀ (by positivity)]
    have h3 : (1 - 1 / (2 * a ^ 2)) * (2 * a) = 2 * a - 1 / a := by field_simp
    rw [h3]
    linarith
  have hlog : Real.arcosh a - (Real.log a + Real.log 2) = Real.log ((a + s) / (2 * a)) := by
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    rw [Real.arcosh, ← hs, Real.log_div (by linarith : (0 : ℝ) < a + s).ne' (by positivity),
      Real.log_mul (by norm_num) ha0.ne']
    ring
  rw [hlog, abs_of_nonpos (Real.log_nonpos hpos.le hr1)]
  have h3 := Real.one_sub_inv_le_log_of_pos hpos
  have hu : 1 / (2 * a ^ 2) ≤ 1 / 2 ^ 57 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h4 : ((a + s) / (2 * a))⁻¹ ≤ 1 + 2 * (1 / (2 * a ^ 2)) := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

theorem sign_zero_test (w : UInt64) : (w >>> 32 >>> 31 == 0) = !Wasm.IEEE64.sign w := by
  rw [← F64UpperWord.sign_test]
  have hlt : (w >>> 32 >>> 31).toNat < 2 := by
    rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight]
    have := w.toNat_lt
    simp only [show (32 : UInt64).toNat % 64 = 32 from rfl,
      show (31 : UInt64).toNat % 64 = 31 from rfl, Nat.shiftRight_eq_div_pow]
    omega
  have hcases : w >>> 32 >>> 31 = 0 ∨ w >>> 32 >>> 31 = 1 := by
    rcases (by omega : (w >>> 32 >>> 31).toNat = 0 ∨ (w >>> 32 >>> 31).toNat = 1) with h | h
    · exact Or.inl (UInt64.toNat_inj.mp (by rw [h]; rfl))
    · exact Or.inr (UInt64.toNat_inj.mp (by rw [h]; rfl))
  rcases hcases with h | h <;> rw [h] <;> decide

/-- `|x| ≥ 2 ^ 28` before the sign. -/
theorem asinh_large_w (x : Float) (hx : Finite x.toBits) (h28 : 2 ^ 28 ≤ |value x.toBits|) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log.log x.abs + ln2F).toBits := by
  obtain ⟨haf, hav⟩ := AtanTheoremReduce.abs_facts x hx
  have h := log_ln2 x.abs haf (by rw [hav]; exact h28) (Real.arsinh |value x.toBits|)
  rw [hav] at h
  exact h ((arsinh_large _ h28).trans (by norm_num))

/-- `x ≥ 2 ^ 28`. -/
theorem acosh_large (x : Float) (hx : Finite x.toBits) (h28 : 2 ^ 28 ≤ value x.toBits) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits)) (Log.log x + ln2F).toBits :=
  log_ln2 x hx h28 _ ((arcosh_large _ h28).trans (by norm_num))

/-- A result for `|x|` with the sign of `x`. -/
theorem signed_two (x w : Float) (f : ℝ → ℝ) (hodd : ∀ v, f (-v) = -f v)
    (hw : F64SignedRounding.WithinSteps 2 (f |value x.toBits|) w.toBits) (hx0 : value x.toBits ≠ 0) :
    F64SignedRounding.WithinSteps 2 (f (value x.toBits))
      (if x.toBits >>> 32 >>> 31 == 0 then w else -w).toBits := by
  have hmag := F64Magnitude.scaledMagnitude_pos x.toBits hx0
  rw [sign_zero_test]
  cases hs : Wasm.IEEE64.sign x.toBits
  · have hpos : 0 ≤ value x.toBits := AtanTwoErr.nonneg_of_sign _ hs
    rw [abs_of_nonneg hpos] at hw
    simpa using hw
  · have hneg := (F64Magnitude.sign_value x.toBits hmag).mp hs
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [F64Bits.toBits_neg, F64Sign.sub_negZero, AtanTheorem.not_nan_of_within 2 _ _ hw]
    simp only [Bool.false_eq_true, ite_false]
    rw [abs_of_neg hneg, hodd] at hw
    have h := (F64SignedRounding.within_negate 2 (-f (value x.toBits)) w.toBits).mpr hw
    rwa [neg_neg] at h

#print axioms log_ln2
#print axioms asinh_large_w
#print axioms acosh_large
#print axioms signed_two

end Verified.Examples.AsinhTheoremLarge
