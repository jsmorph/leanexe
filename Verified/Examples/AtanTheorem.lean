import Verified.Examples.AtanTheoremSmall

/-!
The accuracy theorem for `Atan.atan`.  For every finite binary64 input `x`, the result lies within
one representable step of the nearest-even rounding of `arctan x`.  The proof follows the branches
of fdlibm's code: from `2 ^ 66` on the result is `±π/2` rounded, below `2 ^ -27` it is `x`, below
`0.4375` the polynomial of `AtanTheoremSmall`, and otherwise the reduced arguments of
`AtanTheoremCases`, negated for a negative `x`.
-/

namespace Verified.Examples.AtanTheorem
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound AtanTheoremPoly AtanTheoremBranches
  AtanTheoremTail AtanTheoremConst AtanTheoremReduce AtanTheoremCases AtanTheoremSmall
  F64WithinSelf

set_option exponentiation.threshold 4096

theorem u_lt_of_not_ge (a b : UInt64) (h : ¬ a ≥ b) : a < b := by
  rw [UInt64.lt_iff_toNat_lt]
  rw [ge_iff_le, UInt64.le_iff_toNat_le] at h
  omega

theorem u_not_lt_of_ge (a b : UInt64) (h1 : a ≥ b) (h2 : a < b) : False := by
  rw [UInt64.lt_iff_toNat_lt] at h2
  rw [ge_iff_le, UInt64.le_iff_toNat_le] at h1
  omega

theorem ix_lt (x : Float) (H : ℕ) (hH : H < 2 ^ 31) (q : ℚ)
    (hq : ratOfWord (UInt64.ofNat (H * 2 ^ 32)) = q) :
    ixOf x < UInt64.ofNat H ↔ |value x.toBits| < (q : ℝ) := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (hH.trans (by decide)),
    ← value_word _ q hq]
  exact F64UpperWord.high_lt_iff x.toBits H hH

theorem ix_66 (x : Float) : ixOf x < 0x44100000 ↔ |value x.toBits| < 2 ^ 66 := by
  have h := ix_lt x 0x44100000 (by norm_num) (2 ^ 66) (by decide +kernel)
  push_cast at h
  exact h

theorem ix_27 (x : Float) : ixOf x < 0x3e400000 ↔ |value x.toBits| < 1 / 2 ^ 27 := by
  have h := ix_lt x 0x3e400000 (by norm_num) (1 / 2 ^ 27) (by decide +kernel)
  push_cast at h
  exact h

theorem ix_a (x : Float) : ixOf x < 0x3fdc0000 ↔ |value x.toBits| < 7 / 16 := by
  have h := ix_lt x 0x3fdc0000 (by norm_num) (7 / 16) (by decide +kernel)
  push_cast at h
  exact h

theorem ix_b (x : Float) : ixOf x < 0x3fe60000 ↔ |value x.toBits| < 11 / 16 := by
  have h := ix_lt x 0x3fe60000 (by norm_num) (11 / 16) (by decide +kernel)
  push_cast at h
  exact h

theorem ix_c (x : Float) : ixOf x < 0x3ff30000 ↔ |value x.toBits| < 19 / 16 := by
  have h := ix_lt x 0x3ff30000 (by norm_num) (19 / 16) (by decide +kernel)
  push_cast at h
  exact h

theorem ix_d (x : Float) : ixOf x < 0x40038000 ↔ |value x.toBits| < 39 / 16 := by
  have h := ix_lt x 0x40038000 (by norm_num) (39 / 16) (by decide +kernel)
  push_cast at h
  exact h

theorem not_nan_of_within (n : ℕ) (y : ℝ) (w : UInt64)
    (h : F64SignedRounding.WithinSteps n y w) : Wasm.IEEE64.isNaN w = false := by
  have h1 := h.1
  have hw := w.toNat_lt
  simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_false_iff,
    beq_eq_false_iff_ne, bne_eq_false_iff_eq]
  omega

/-- A result for `|x|`, negated for a negative `x`. -/
theorem signed_result (x z : Float) (hx0 : value x.toBits ≠ 0)
    (hz : F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|) z.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits))
      (if x.toBits >>> 32 >>> 31 == 1 then -z else z).toBits := by
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x.toBits) with h0 | h0
    · exfalso
      apply hx0
      simp only [value, Wasm.IEEE64.scaledValue, h0]
      split <;> simp
    · exact h0
  rw [F64UpperWord.sign_test]
  cases hs : Wasm.IEEE64.sign x.toBits
  · have hpos : 0 ≤ value x.toBits := by
      by_contra hn
      have := (F64Magnitude.sign_value x.toBits hmag).mpr (lt_of_not_ge hn)
      rw [hs] at this
      exact Bool.false_ne_true this
    simp only [Bool.false_eq_true, ite_false]
    rwa [abs_of_nonneg hpos] at hz
  · have hneg := (F64Magnitude.sign_value x.toBits hmag).mp hs
    simp only [ite_true]
    rw [F64Bits.toBits_neg, F64Sign.sub_negZero, not_nan_of_within 1 _ _ hz]
    simp only [Bool.false_eq_true, ite_false]
    rw [abs_of_neg hneg, Real.arctan_neg] at hz
    have h := (F64SignedRounding.within_negate 1 (-Real.arctan (value x.toBits)) z.toBits).mpr hz
    rwa [neg_neg] at h

theorem big_bits :
    (Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x3C91A62633145C07).toBits =
      0x3FF921FB54442D18 := by
  rw [F64Bits.toBits_add, F64Bits.toBits_ofBits, F64Bits.toBits_ofBits]
  decide +kernel

theorem big_neg_bits :
    (-Float.ofBits 0x3FF921FB54442D18 - Float.ofBits 0x3C91A62633145C07).toBits =
      Wasm.IEEE64.negate 0x3FF921FB54442D18 := by
  rw [F64Bits.toBits_sub, F64Bits.toBits_neg, F64Bits.toBits_ofBits, F64Bits.toBits_ofBits]
  decide +kernel

theorem atan_big_eq (x : Float) (hx : Finite x.toBits) (h1 : ixOf x ≥ 0x44100000) :
    Atan.atan x = if x.toBits >>> 32 >>> 31 == 1 then
        -Float.ofBits 0x3FF921FB54442D18 - Float.ofBits 0x3C91A62633145C07
      else Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x3C91A62633145C07 := by
  have hf := F64UpperWord.finite_high x.toBits hx
  have hn1 : ¬ ixOf x > 0x7ff00000 := by
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    rw [show (0x7ff00000 : UInt64).toNat = 0x7ff00000 from rfl] at this
    unfold ixOf at this
    omega
  have hn2 : (ixOf x == 0x7ff00000) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg UInt64.toNat h
    rw [show (0x7ff00000 : UInt64).toNat = 0x7ff00000 from rfl] at this
    unfold ixOf at this
    omega
  unfold ixOf at h1 hn1 hn2
  simp only [Atan.atan, h1, hn1, hn2, ite_true, decide_false, Bool.false_or, Bool.false_and,
    Bool.false_eq_true, ite_false]

/-- The value of `atanhi[3]` within `6.2 · 10 ^ -17` of `π/2`. -/
theorem big_close : |value 0x3FF921FB54442D18 - Real.pi / 2| ≤ 62 / 10 ^ 18 := by
  have h := atan_inf
  have hl := word_eq 0x3C91A62633145C07 (4967757600021511 / 81129638414606681695789005144064 : ℚ)
    (by decide +kernel)
  rw [hl] at h
  push_cast at h
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [h.1, h.2]

theorem atan_big (x : Float) (hx : Finite x.toBits) (h1 : ixOf x ≥ 0x44100000) :
    F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits)) (Atan.atan x).toBits := by
  have hge : 2 ^ 66 ≤ |value x.toBits| :=
    not_lt.mp (fun h => u_not_lt_of_ge _ _ h1 ((ix_66 x).mpr h))
  have hx0 : value x.toBits ≠ 0 := by
    intro h
    rw [h, abs_zero] at hge
    norm_num at hge
  rw [atan_big_eq x hx h1]
  have hz : F64SignedRounding.WithinSteps 1 (Real.arctan |value x.toBits|)
      (Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x3C91A62633145C07).toBits := by
    rw [big_bits]
    set a := |value x.toBits|
    have ha : 0 < a := lt_of_lt_of_le (by positivity) hge
    have hinv := Real.arctan_inv_of_pos ha
    have hs : Real.arctan a = Real.pi / 2 - Real.arctan a⁻¹ := by linarith
    have hi0 : 0 ≤ Real.arctan a⁻¹ := by
      have := Real.arctan_mono (inv_nonneg.mpr ha.le)
      rwa [Real.arctan_zero] at this
    have hi1 : Real.arctan a⁻¹ ≤ 1 / 2 ^ 66 := by
      have := abs_arctan_le a⁻¹
      rw [abs_of_nonneg hi0, abs_of_nonneg (inv_nonneg.mpr ha.le)] at this
      refine this.trans ?_
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) hge
    have hc := big_close
    have hp := pi_close
    refine within_one_of_error _ _ 1023 (by norm_num) (62 / 10 ^ 18 + 1 / 2 ^ 66)
      (by unfold CodeLib.IEEE64.Finite; decide +kernel) ?_ ?_ (by norm_num) ?_
    · rw [hs]
      rw [abs_le] at hc ⊢
      constructor <;> linarith [hc.1, hc.2]
    · rw [F64PositiveSpacing.boundary_value 1023 (by norm_num) (by norm_num), hs]
      rw [abs_le] at hp
      norm_num
      linarith [hp.1, hp.2]
    · rw [hs]
      rw [abs_le] at hp
      norm_num
      linarith [hp.1, hp.2]
  have hzf : Wasm.IEEE64.isNaN
      (Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x3C91A62633145C07).toBits = false := by
    rw [big_bits]
    decide +kernel
  have h := signed_result x (Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x3C91A62633145C07)
    hx0 hz
  rw [F64UpperWord.sign_test] at h ⊢
  cases hs : Wasm.IEEE64.sign x.toBits
  · simpa [hs] using h
  · simp only [hs, ite_true] at h ⊢
    rw [big_neg_bits]
    rw [F64Bits.toBits_neg, F64Sign.sub_negZero, hzf, big_bits] at h
    simpa using h

theorem huge_gt (x : Float) (hx : Finite x.toBits) (hs : |value x.toBits| < 1) :
    Float.ofBits 0x7E37E43C8800759C + x > 1.0 := by
  have hh : (10 : ℝ) ^ 299 ≤ value 0x7E37E43C8800759C := by
    rw [value_word 0x7E37E43C8800759C (ratOfWord 0x7E37E43C8800759C) rfl]
    have : (10 ^ 299 : ℚ) ≤ ratOfWord 0x7E37E43C8800759C := by decide +kernel
    exact_mod_cast this
  have hh2 : value 0x7E37E43C8800759C ≤ (10 : ℝ) ^ 301 := by
    rw [value_word 0x7E37E43C8800759C (ratOfWord 0x7E37E43C8800759C) rfl]
    have : ratOfWord 0x7E37E43C8800759C ≤ (10 ^ 301 : ℚ) := by decide +kernel
    exact_mod_cast this
  have hf : Wasm.IEEE64.isFinite 0x7E37E43C8800759C = true := by decide +kernel
  have hpos : (0 : ℝ) < value 0x7E37E43C8800759C := lt_of_lt_of_le (by positivity) hh
  have hB : |value 0x7E37E43C8800759C + value x.toBits| + (0 + 0) ≤ (10 : ℝ) ^ 302 := by
    have h1 := abs_add_le (value 0x7E37E43C8800759C) (value x.toBits)
    rw [abs_of_pos hpos] at h1
    have h2 : (10 : ℝ) ^ 301 + 1 ≤ 10 ^ 302 := by norm_num
    linarith
  have hx' : FApprox x (value x.toBits) 0 := approx_self _ hx
  have ha := fapprox_add (fapprox_ofBits _ hf) hx' _ hB (by norm_num)
  rw [gt_iff_lt, F64UpperWord.float_lt_iff _ _ one_finite ha.1, one_value]
  have hl := ha.lower
  have hs' := (abs_lt.mp hs).1
  have h3 : (0 : ℝ) + 0 + 10 ^ 302 / 2 ^ 53 ≤ 10 ^ 298 := by norm_num
  have h4 : (2 : ℝ) ≤ 10 ^ 299 - 10 ^ 298 := by norm_num
  linarith

/-- The accuracy of `Atan.atan`: for every finite input the result lies within one representable
step of the nearest-even rounding of `arctan x`. -/
theorem atan_within_one (x : Float) (hx : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.arctan (value x.toBits)) (Atan.atan x).toBits := by
  set v := value x.toBits with hv
  by_cases h1 : ixOf x ≥ 0x44100000
  · exact atan_big x hx h1
  by_cases h2 : ixOf x < 0x3e400000
  · have hs := (ix_27 x).mp h2
    rw [atan_tiny_eq x h2 (huge_gt x hx (hs.trans (by norm_num)))]
    exact atan_tiny x hx hs
  have hge : 1 / 2 ^ 27 ≤ |v| := not_lt.mp (fun h => h2 ((ix_27 x).mpr h))
  have hlt66 : |v| < 2 ^ 66 := (ix_66 x).mp (u_lt_of_not_ge _ _ h1)
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, abs_zero] at hge
    norm_num at hge
  by_cases h3 : ixOf x < 0x3fdc0000
  · rw [atan_poly_eq x h1 h2 h3]
    have hlt := (ix_a x).mp h3
    rcases le_or_gt |v| (1 / 4) with ha | ha
    · exact atan_poly_small x hx hge ha
    rcases le_or_gt |v| (2556 / 10000) with hb | hb
    · exact atan_poly_mid_a x hx ha.le hb
    · exact atan_poly_mid_b x hx hb.le hlt.le
  have hA : 7 / 16 ≤ |v| := not_lt.mp (fun h => h3 ((ix_a x).mpr h))
  by_cases h4 : ixOf x < 0x3ff30000
  · have hc := (ix_c x).mp h4
    by_cases h5 : ixOf x < 0x3fe60000
    · have hb := (ix_b x).mp h5
      rw [atan_tail0_eq x h1 h3 h4 h5]
      apply signed_result x _ hv0
      rcases le_or_gt |v| (551 / 1000) with hm | hm
      · exact case0_low x hx hA hm
      · exact case0_high x hx hm.le hb.le
    · have hB : 11 / 16 ≤ |v| := not_lt.mp (fun h => h5 ((ix_b x).mpr h))
      rw [atan_tail1_eq x h1 h3 h4 h5]
      apply signed_result x _ hv0
      rcases le_or_gt |v| 1 with hm | hm
      · exact case1_low x hx hB hm
      · exact case1_high x hx hm.le hc.le
  · have hC : 19 / 16 ≤ |v| := not_lt.mp (fun h => h4 ((ix_c x).mpr h))
    by_cases h6 : ixOf x < 0x40038000
    · have hd := (ix_d x).mp h6
      rw [atan_tail2_eq x h1 h3 h4 h6]
      apply signed_result x _ hv0
      rcases le_or_gt |v| (3 / 2) with hm | hm
      · exact case2_a x hx hC hm
      rcases le_or_gt |v| (793 / 500) with hm2 | hm2
      · exact case2_b x hx hm.le hm2
      · exact case2_c x hx hm2.le hd.le
    · have hD : 39 / 16 ≤ |v| := not_lt.mp (fun h => h6 ((ix_d x).mpr h))
      rw [atan_tail3_eq x h1 h3 h4 h6]
      apply signed_result x _ hv0
      exact case3 x hx hD (by norm_num; linarith)

#print axioms atan_big
#print axioms atan_within_one

end Verified.Examples.AtanTheorem
