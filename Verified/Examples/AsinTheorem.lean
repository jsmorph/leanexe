import Verified.Examples.AsinTheoremMid
import Verified.Examples.AtanTheoremSpecial

/-!
`Asin.asin x` within one step of `arcsin x` for every finite `x` with `|x| ≤ 1`.  The proof
follows the code's branches on the high word of `|x|`: `±1` gives `±π/2` rounded, below `2 ^ -26`
the result is `x`, below `1/2` it is `x + x r(x²)`, and from `1/2` on the half-angle forms of
`AsinTheoremMid` and `AsinTheoremBig` give `arcsin |x|`, negated for a negative `x`.
-/

namespace Verified.Examples.AsinTheorem
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound AsinTheoremSupport AsinTheoremRatio
  AsinTheoremBranches AsinTheoremSmall AsinTheoremHalf AsinTheoremBig AsinTheoremMid

set_option exponentiation.threshold 4096

theorem ixA_lt (x : Float) (H : ℕ) (hH : H < 2 ^ 31) (q : ℚ)
    (hq : ratOfWord (UInt64.ofNat (H * 2 ^ 32)) = q) :
    ixA x < UInt64.ofNat H ↔ |value x.toBits| < (q : ℝ) := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (hH.trans (by decide)),
    ← AtanTheoremReduce.value_word _ q hq]
  exact F64UpperWord.high_lt_iff x.toBits H hH

theorem arcsin_ge_half (a : ℝ) (h : 1 / 2 ≤ a) (h1 : a ≤ 1) : 5233 / 10000 ≤ Real.arcsin a := by
  have hs : Real.arcsin (1 / 2) = Real.pi / 6 := by
    rw [← Real.sin_pi_div_six, Real.arcsin_sin (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])]
  have hm := Real.arcsin_le_arcsin h
  have hp := Real.pi_gt_d2
  rw [hs] at hm
  linarith

theorem arcsin_ge_nine (a : ℝ) (h : 9 / 10 ≤ a) (h1 : a ≤ 1) : 1 + 1 / 100 ≤ Real.arcsin a := by
  have hb := Real.sin_bound (x := 1) (by norm_num)
  have hs1 : Real.sin 1 ≤ 8855 / 10000 := by
    have := (abs_le.mp hb).2
    norm_num at this ⊢
    linarith
  have hs0 : 0 ≤ Real.sin 1 := Real.sin_nonneg_of_nonneg_of_le_pi (by norm_num)
    (by linarith [Real.pi_gt_three])
  have hone : Real.arcsin (Real.sin 1) = 1 :=
    Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])
  have hm1 : 1 ≤ Real.arcsin (9 / 10) := by
    rw [← hone]
    exact Real.arcsin_le_arcsin (by linarith)
  have hd := Real.abs_sin_sub_sin_le (Real.arcsin (9 / 10)) (Real.arcsin (Real.sin 1))
  rw [Real.sin_arcsin (by norm_num) (by norm_num), Real.sin_arcsin (by linarith) (by linarith),
    hone, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hd
  have hm := Real.arcsin_le_arcsin h
  linarith

theorem signed_asin (x z : Float) (hx0 : value x.toBits ≠ 0)
    (hz : F64SignedRounding.WithinSteps 1 (Real.arcsin |value x.toBits|) z.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin (value x.toBits))
      (if x.toBits >>> 32 >>> 31 == 0 then z else -z).toBits := by
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x.toBits) with h0 | h0
    · exfalso
      apply hx0
      simp only [value, Wasm.IEEE64.scaledValue, h0]
      split <;> simp
    · exact h0
  have h01 : (x.toBits >>> 32 >>> 31 == 0) = !(x.toBits >>> 32 >>> 31 == 1) := by
    have hlt : (x.toBits >>> 32 >>> 31).toNat < 2 := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight]
      have := x.toBits.toNat_lt
      simp only [show (32 : UInt64).toNat % 64 = 32 from rfl,
        show (31 : UInt64).toNat % 64 = 31 from rfl, Nat.shiftRight_eq_div_pow]
      omega
    have hcases : x.toBits >>> 32 >>> 31 = 0 ∨ x.toBits >>> 32 >>> 31 = 1 := by
      rcases (by omega : (x.toBits >>> 32 >>> 31).toNat = 0 ∨
          (x.toBits >>> 32 >>> 31).toNat = 1) with h | h
      · exact Or.inl (UInt64.toNat_inj.mp (by rw [h]; rfl))
      · exact Or.inr (UInt64.toNat_inj.mp (by rw [h]; rfl))
    rcases hcases with h | h <;> rw [h] <;> decide
  rw [h01, F64UpperWord.sign_test]
  cases hs : Wasm.IEEE64.sign x.toBits
  · have hpos : 0 ≤ value x.toBits := by
      by_contra hn
      have := (F64Magnitude.sign_value x.toBits hmag).mpr (lt_of_not_ge hn)
      rw [hs] at this
      exact Bool.false_ne_true this
    simp only [Bool.not_false, ite_true]
    rwa [abs_of_nonneg hpos] at hz
  · have hneg := (F64Magnitude.sign_value x.toBits hmag).mp hs
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [F64Bits.toBits_neg, F64Sign.sub_negZero, AtanTheorem.not_nan_of_within 1 _ _ hz]
    simp only [Bool.false_eq_true, ite_false]
    rw [abs_of_neg hneg, Real.arcsin_neg] at hz
    have h := (F64SignedRounding.within_negate 1 (-Real.arcsin (value x.toBits)) z.toBits).mpr hz
    rwa [neg_neg] at h

theorem ix_one (x : Float) : ixA x < 0x3ff00000 ↔ |value x.toBits| < 1 := by
  have h := ixA_lt x 0x3ff00000 (by norm_num) 1 (by decide +kernel)
  push_cast at h
  exact h

theorem ix_26 (x : Float) : ixA x < 0x3e500000 ↔ |value x.toBits| < 1 / 2 ^ 26 := by
  have h := ixA_lt x 0x3e500000 (by norm_num) (1 / 2 ^ 26) (by decide +kernel)
  push_cast at h
  exact h

theorem ix_half (x : Float) : ixA x < 0x3fe00000 ↔ |value x.toBits| < 1 / 2 := by
  have h := ixA_lt x 0x3fe00000 (by norm_num) (1 / 2) (by decide +kernel)
  push_cast at h
  exact h

theorem ix_big (x : Float) : ixA x < 0x3FEF3333 ↔ |value x.toBits| < 2044723 / 2097152 := by
  have h := ixA_lt x 0x3FEF3333 (by norm_num) (2044723 / 2097152) (by decide +kernel)
  push_cast at h
  exact h

theorem within_zero_one {y : ℝ} {w : UInt64} (h : F64SignedRounding.WithinSteps 0 y w) :
    F64SignedRounding.WithinSteps 1 y w :=
  ⟨h.1, h.2.trans (by norm_num)⟩

/-- A word of magnitude one is `1` or `-1`. -/
theorem unit_bits (x : Float) (h : |value x.toBits| = 1) :
    x.toBits = 0x3FF0000000000000 ∨ x.toBits = 0xBFF0000000000000 := by
  have hone : value (0x3FF0000000000000 : UInt64) = 1 := by
    rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x3FF0000000000000 = 1 by
      decide +kernel]
    norm_num
  have ha : value (Wasm.IEEE64.abs x.toBits) = value (0x3FF0000000000000 : UInt64) := by
    rw [F64UpperWord.value_abs, h, hone]
  have hat := F64UpperWord.abs_toNat x.toBits
  have hlt : (Wasm.IEEE64.abs x.toBits).toNat < 2 ^ 63 := by rw [hat]; omega
  have hc : (0x3FF0000000000000 : UInt64).toNat = 4607182418800017408 := rfl
  have h1 := (F64PositiveOrder.value_le_iff hlt (by rw [hc]; norm_num)).mp ha.le
  have h2 := (F64PositiveOrder.value_le_iff (by rw [hc]; norm_num) hlt).mp ha.ge
  rw [hat, hc] at h1 h2
  have hn := x.toBits.toNat_lt
  rcases Nat.lt_or_ge x.toBits.toNat (2 ^ 63) with hs | hs
  · left
    apply UInt64.toNat_inj.mp
    rw [hc]
    omega
  · right
    apply UInt64.toNat_inj.mp
    rw [show (0xBFF0000000000000 : UInt64).toNat = 13830554455654793216 from rfl]
    omega

/-- `±1` give `±π/2` rounded to nearest. -/
theorem asin_unit (x : Float) (h : |value x.toBits| = 1) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin (value x.toBits)) (Asin.asin x).toBits := by
  rcases unit_bits x h with hb | hb
  · have hv : value x.toBits = 1 := by
      rw [hb, ← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x3FF0000000000000 = 1 by
        decide +kernel]
      norm_num
    have he : (Asin.asin x).toBits = 0x3FF921FB54442D18 := by
      rw [asin_one_eq x (by unfold ixA; rw [hb]; decide) (by unfold ixA lxA; rw [hb]; decide),
        F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_mul, hb]
      unfold pio2HiF pio2LoF
      rw [F64Bits.toBits_ofBits, F64Bits.toBits_ofBits]
      decide +kernel
    rw [he, hv, Real.arcsin_one]
    exact within_zero_one AtanTheoremSpecial.half_pi_ref
  · have hv : value x.toBits = -1 := by
      rw [hb, ← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0xBFF0000000000000 = -1 by
        decide +kernel]
      norm_num
    have he : (Asin.asin x).toBits = 0xBFF921FB54442D18 := by
      rw [asin_one_eq x (by unfold ixA; rw [hb]; decide) (by unfold ixA lxA; rw [hb]; decide),
        F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_mul, hb]
      unfold pio2HiF pio2LoF
      rw [F64Bits.toBits_ofBits, F64Bits.toBits_ofBits]
      decide +kernel
    rw [he, hv, Real.arcsin_neg_one,
      show (0xBFF921FB54442D18 : UInt64) = Wasm.IEEE64.negate 0x3FF921FB54442D18 by decide]
    exact (F64SignedRounding.within_negate 1 (Real.pi / 2) _).mpr
      (within_zero_one AtanTheoremSpecial.half_pi_ref)

/-- `x + x r(x²)` for `2 ^ -26 ≤ |x| < 1/2`. -/
theorem small_within (x : Float) (hx : Finite x.toBits) (h0 : 1 / 2 ^ 26 ≤ |value x.toBits|)
    (h1 : |value x.toBits| < 1 / 2) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin (value x.toBits))
      (x + x * Asin.asinRatio (x * x)).toBits := by
  have hσp : 0 < |value x.toBits| := lt_of_lt_of_le (by positivity) h0
  have hfx := fsapprox_input x hx |value x.toBits| hσp (by linarith) le_rfl
  have hss : 1 / 2 ^ 52 ≤ |value x.toBits| * |value x.toBits| := by
    have := mul_le_mul h0 h0 (by positivity) hσp.le
    norm_num at this ⊢
    linarith
  have hη : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (|value x.toBits| * |value x.toBits|) := by
    have := mul_le_mul_of_nonneg_left hss (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 960)
    norm_num at this ⊢
    linarith
  have ht := (fsapprox_mul hfx hfx (1 / 2 ^ 960) hη (by norm_num)).mono (M' := 1)
    (e' := (10001 / 10000) / 2 ^ 53) (by norm_num) (by norm_num)
  have hvv : value x.toBits * value x.toBits = |value x.toBits| * |value x.toBits| :=
    (abs_mul_abs_self _).symm
  have hσ0 : 1 / 2 ^ 54 ≤ |value x.toBits| * |value x.toBits| := le_trans (by norm_num) hss
  have hσ4 : |value x.toBits| * |value x.toBits| ≤ 1 / 4 := by
    have := mul_le_mul h1.le h1.le hσp.le (by norm_num)
    norm_num at this ⊢
    linarith
  rcases le_or_gt (|value x.toBits| * |value x.toBits|) (1 / 8) with hs | hs
  · have hr := ratio_S1 (x * x) _ _ ht (mul_self_nonneg _) (by rw [hvv]; exact hs) hs
      hσ0
    rw [ratio_eval] at hr
    exact small_finish x hx (1 / 8) _ _ ((9 / 10) / 2 ^ 53) hr (by norm_num) (by norm_num) hs h0 h1
      (by norm_num) (by norm_num)
  · have hr := ratio_S2 (x * x) _ _ ht (by rw [hvv]; exact hs.le) (by rw [hvv]; exact hσ4)
      hσ4 hσ0
    rw [ratio_eval] at hr
    exact small_finish x hx (1 / 4) _ _ ((9 / 10) / 2 ^ 53) hr (by norm_num) (by norm_num) hσ4 h0
      h1 (by norm_num) (by norm_num)

/-- The accuracy of `Asin.asin`: for every finite input with `|x| ≤ 1` the result lies within one
representable step of the nearest-even rounding of `arcsin x`. -/
theorem asin_within_one (x : Float) (hx : Finite x.toBits) (hdom : |value x.toBits| ≤ 1) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin (value x.toBits)) (Asin.asin x).toBits := by
  by_cases h1 : ixA x ≥ 0x3ff00000
  · have hge : 1 ≤ |value x.toBits| :=
      not_lt.mp (fun h => AtanTheorem.u_not_lt_of_ge _ _ h1 ((ix_one x).mpr h))
    exact asin_unit x (le_antisymm hdom hge)
  have hlt1 : |value x.toBits| < 1 := (ix_one x).mp (AtanTheorem.u_lt_of_not_ge _ _ h1)
  by_cases h2 : ixA x < 0x3fe00000
  · have hhalf := (ix_half x).mp h2
    by_cases h3 : ixA x < 0x3e500000
    · have hs := (ix_26 x).mp h3
      rw [asin_tiny_eq x h1 h2 h3 (AtanTheorem.huge_gt x hx hlt1)]
      exact tiny_within x hx hs
    · have hge : 1 / 2 ^ 26 ≤ |value x.toBits| := not_lt.mp (fun h => h3 ((ix_26 x).mpr h))
      rw [asin_small_eq x h1 h2 h3]
      exact small_within x hx hge hhalf
  have hge : 1 / 2 ≤ |value x.toBits| := not_lt.mp (fun h => h2 ((ix_half x).mpr h))
  have hv0 : value x.toBits ≠ 0 := by
    intro h
    rw [h, abs_zero] at hge
    norm_num at hge
  by_cases h3 : ixA x ≥ 0x3FEF3333
  · have hb : 2044723 / 2097152 ≤ |value x.toBits| :=
      not_lt.mp (fun h => AtanTheorem.u_not_lt_of_ge _ _ h3 ((ix_big x).mpr h))
    rw [asin_big_eq x h1 h2 h3]
    exact signed_asin x _ hv0 (big_within x hx (le_trans (by norm_num) hb) hlt1)
  have hb := (ix_big x).mp (AtanTheorem.u_lt_of_not_ge _ _ h3)
  rw [asin_mid_eq x h1 h2 h3]
  apply signed_asin x _ hv0
  rcases le_or_gt |value x.toBits| (3 / 5) with hm | hm
  · exact mid_A x hx hge hm
      (le_trans (by norm_num) (arcsin_ge_half |value x.toBits| hge hlt1.le))
  rcases le_or_gt |value x.toBits| (9 / 10) with hm2 | hm2
  · exact mid_B x hx hm.le hm2
      (le_trans (by norm_num) (arcsin_ge_half |value x.toBits| hge hlt1.le))
  · exact mid_C x hx hm2.le (le_trans hb.le (by norm_num))
      (le_trans (by norm_num) (arcsin_ge_nine |value x.toBits| hm2.le hlt1.le))

#print axioms asin_within_one

end Verified.Examples.AsinTheorem
