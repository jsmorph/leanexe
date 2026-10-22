import Library.Numerics.Float64.Tgamma.TgammaTiny
import Library.Numerics.Float64.Tgamma.TgammaMainRed
import LeanExe.ProofKit.F64RelativeSteps
import LeanExe.ProofKit.GammaThresholds

/-!
The overflow, underflow, and pole results of `tgammaWith`.  From `0x1.573fae561f648p+7` on, the code
adds two copies of `0x7FEF000000000000`, a sum above the overflow threshold, so the result is `+∞`,
which is within one step of `Γ x ≥ 2 ^ 1024` (`GammaThresholds.gamma_overflow`, `overflowPath_within`).
At or below -184, the code multiplies `2 ^ -1022` by `±2 ^ -1022`, which rounds to a zero, and a zero
of either sign is within one step of `Γ x`, which lies below `2 ^ -1078` in magnitude
(`GammaBasic.gamma_underflow`, `underflowPath_within`).  At the negative integers the code divides
zero by zero, which gives the canonical NaN (`intPath_neg`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaEdge
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaDD TgammaTop TgammaTiny TgammaRecip TgammaFloor
  TgammaWords TgammaMainRed

set_option exponentiation.threshold 4096

theorem word_value (w : UInt64) (q : ℚ) (hf : Wasm.IEEE64.isFinite w = true)
    (h : PolyBound.ratOfWord w = q) : value (Float.ofBits w).toBits = (q : ℝ) := by
  rw [ofBits_value w hf, h]

/-- **The overflow path**: `+∞`, within one step of `Γ x` from the threshold on. -/
theorem overflowPath_within (y : ℝ) (hy : (GammaThresholds.t0 : ℝ) ≤ y) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma y) TgammaBranches.overflowPath.toBits := by
  have hf : Wasm.IEEE64.isFinite 0x7FEF000000000000 = true := by decide
  have hv := word_value 0x7FEF000000000000 (31 * 2 ^ 1019) hf (by decide +kernel)
  unfold TgammaBranches.overflowPath
  rw [F64Bits.toBits_add, add_overflow _ _ (ofBits_finite _ hf) (ofBits_finite _ hf)
    (by rw [hv]; norm_num)]
  apply within_pos_inf
  have := GammaThresholds.gamma_overflow hy
  have hthr : F64PositiveRounding.overflowThreshold = 2 ^ 1024 - 2 ^ 970 := rfl
  rw [hthr]
  linarith [(by norm_num : (0 : ℝ) ≤ 2 ^ 970)]

theorem position_zero (neg : Bool) :
    F64SignedRounding.position (Wasm.IEEE64.encodeFinite neg 0 0) = 0 := by
  cases neg <;> decide

/-- A zero of either sign is within one step of every `y` below the least subnormal. -/
theorem within_zero (y : ℝ) (hy : |y| < 1 / 2 ^ 1074) (neg : Bool) :
    F64SignedRounding.WithinSteps 1 y (Wasm.IEEE64.encodeFinite neg 0 0) := by
  have h0v : value (0 : UInt64) = 0 := by
    rw [TgammaSpecial.lit_value 0 0 (by decide +kernel)]
    norm_num
  have hw := F64RelativeSteps.within_steps_low 1 le_rfl (by norm_num) |y| (abs_nonneg _) 0
    (by unfold CodeLib.IEEE64.Finite; decide) (by decide)
    (by rw [h0v, zero_sub, abs_neg, abs_abs]; linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 1074)])
  obtain ⟨-, hw2⟩ := hw
  have hp0 : F64SignedRounding.position (0 : UInt64) = 0 := by decide
  rw [hp0, zero_sub, abs_neg] at hw2
  refine ⟨by cases neg <;> decide, ?_⟩
  rw [position_zero, zero_sub, abs_neg]
  rcases le_or_gt 0 y with hy0 | hy0
  · rw [abs_of_nonneg hy0] at hw2
    exact hw2
  · have hr : F64SignedRounding.roundNearestEven y =
        Wasm.IEEE64.negate (F64SignedRounding.roundNearestEven (-y)) := by
      unfold F64SignedRounding.roundNearestEven
      rw [ite_eq_right (not_le.mpr hy0), ite_eq_left (by linarith : (0 : ℝ) ≤ -y)]
    rw [abs_of_neg hy0] at hw2
    rw [hr, F64SignedRounding.position_negate, abs_neg]
    exact hw2

/-- A finite product of two nonzero words whose exact value is below half the least subnormal is
a zero. -/
theorem mul_tiny (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0) (hb0 : Wasm.IEEE64.scaledMagnitude b ≠ 0)
    (h : Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b < 2 ^ 1073) :
    Wasm.IEEE64.mul a b =
      Wasm.IEEE64.encodeFinite (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) 0 0 := by
  have hMa0 : (Wasm.IEEE64.scaledMagnitude a == 0) = false := by simpa using ha0
  have hMb0 : (Wasm.IEEE64.scaledMagnitude b == 0) = false := by simpa using hb0
  simp only [Wasm.IEEE64.mul, not_nan_of_finite ha, not_nan_of_finite hb,
    not_infinite_of_finite ha, not_infinite_of_finite hb, hMa0, hMb0, Bool.or_false,
    Bool.false_eq_true, ite_false]
  exact F64Saturate.round_dyadic_zero _ _ (Nat.mul_pos (Nat.pos_of_ne_zero ha0)
    (Nat.pos_of_ne_zero hb0)) h

/-- **The underflow path**: a zero, within one step of `Γ x` at or below -184. -/
theorem underflowPath_within (x : Float) (hx : Finite x.toBits) (h : value x.toBits ≤ -184)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (TgammaBranches.underflowPath x).toBits := by
  -- `Γ x` is below `2 ^ -1078`
  have hgap : 1 / 2 ^ 45 ≤ |value x.toBits - round (value x.toBits)| := by
    obtain ⟨K, hK⟩ := grid x.toBits hx 1028 (by norm_num) (by
      rw [abs_of_neg (by linarith)]
      norm_num
      linarith)
    have hKv : (K : ℝ) = value x.toBits * 2 ^ 45 := by
      have h' : (K : ℝ) * 2 ^ 1029 = value x.toBits * 2 ^ 45 * 2 ^ 1029 := by
        linear_combination -1 * hK
      exact mul_right_cancel₀ (by positivity) h'
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : ℝ) = round (value x.toBits) := ⟨round (value x.toBits), by simp⟩
    have hz : K - m * 2 ^ 45 ≠ 0 := by
      intro h0
      apply hint m
      have : (K : ℝ) - m * 2 ^ 45 = 0 := by exact_mod_cast h0
      linarith
    have h1 : (1 : ℝ) ≤ |((K - m * 2 ^ 45 : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hz
    have e : ((K - m * 2 ^ 45 : ℤ) : ℝ) = (value x.toBits - round (value x.toBits)) * 2 ^ 45 := by
      push_cast
      rw [hKv, hm]
      ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 45)] at h1
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hG := GammaBasic.gamma_underflow h hgap
  -- the product rounds to a zero
  have hf : Wasm.IEEE64.isFinite 0x0010000000000000 = true := by decide
  have htb : (Float.ofBits 0x0010000000000000).toBits = 0x0010000000000000 := ofBits_bits _ hf
  have hm : Wasm.IEEE64.scaledMagnitude 0x0010000000000000 = 2 ^ 52 := by decide
  obtain ⟨hnf, hnv⟩ := neg_float (Float.ofBits 0x0010000000000000) (ofBits_finite _ hf)
  have hnm : Wasm.IEEE64.scaledMagnitude (-(Float.ofBits 0x0010000000000000)).toBits = 2 ^ 52 := by
    have h1 := F64RoundNearest.abs_value (-(Float.ofBits 0x0010000000000000)).toBits
    have h2 := F64RoundNearest.abs_value (Float.ofBits 0x0010000000000000).toBits
    rw [hnv, abs_neg, h2, htb, hm] at h1
    have h3 := (div_left_inj' (by positivity : (2 : ℝ) ^ 1074 ≠ 0)).mp h1
    exact_mod_cast h3.symm
  unfold TgammaBranches.underflowPath
  dsimp only
  have hGt : |Real.Gamma (value x.toBits)| < 1 / 2 ^ 1074 := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1078 ≤ 1 / 2 ^ 1074)]
  split_ifs
  · rw [F64Bits.toBits_mul, htb, mul_tiny _ _ hf hf (by rw [hm]; norm_num) (by rw [hm]; norm_num)
      (by rw [hm]; norm_num)]
    exact within_zero _ hGt _
  · rw [F64Bits.toBits_mul, htb, mul_tiny _ _ hf hnf (by rw [hm]; norm_num) (by rw [hnm]; norm_num)
      (by rw [hm, hnm]; norm_num)]
    exact within_zero _ hGt _

/-- **The negative integers**: the canonical NaN. -/
theorem intPath_neg (x : Float) (hx : Finite x.toBits) (hneg : value x.toBits < 0) :
    (TgammaBranches.intPath x).toBits = Wasm.IEEE64.canonicalNaN := by
  unfold TgammaBranches.intPath
  dsimp only
  have hz : ¬ ((x == 0.0) = true) := by
    rw [TgammaSpecial.zero_test x hx]; exact hneg.ne
  have hlt : x < 0.0 := by
    rw [F64UpperWord.float_lt_iff _ _ hx zero_finite, zero_value]; exact hneg
  rw [ite_eq_right hz, ite_eq_left hlt, F64Bits.toBits_div]
  have hzb := TgammaSpecial.zero_bits
  rw [hzb]
  exact F64Saturate.div_zero_zero 0 0 (by unfold CodeLib.IEEE64.Finite; decide)
    (by unfold CodeLib.IEEE64.Finite; decide) (by decide) (by decide)

#print axioms overflowPath_within
#print axioms within_zero
#print axioms underflowPath_within
#print axioms intPath_neg

end Library.Numerics.Float64.Tgamma.TgammaEdge
