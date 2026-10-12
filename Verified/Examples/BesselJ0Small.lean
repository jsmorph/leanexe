import Verified.Examples.BesselSmallJ0Form2

/-!
`Bessel.j0 x` for `|x| < 2`: the result is finite and lies within `(235/100) u` of `J₀(x)`, with
`u = 2 ^ -53` (`j0_small`).  Of the four paths of `BesselSmallJ0`, the first two need only
`BesselSmallJ0.j0_quad`, the third `BesselSmallJ0.form1` (`2 u`), and the fourth the pieces of
`BesselSmallJ0Form2`, at most `2.227 u` (`form2_all`); `BesselSmallApprox.j0_approx` adds the error
of fdlibm's approximation, `0.12 u + 2^-99`.
-/

namespace Verified.Examples.BesselJ0Small
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS BesselSmallEval BesselSmallApprox BesselJ0Large BesselSmallJ0
  BesselSmallJ0Form2
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The second form for `1 ≤ x < 2`, from the five pieces. -/
theorem form2_all (xa : Float) (hf : Finite xa.toBits) (hs : Wasm.IEEE64.sign xa.toBits = false)
    (he : 2 ≤ Wasm.IEEE64.exponent xa.toBits) (v : ℝ) (hv : value xa.toBits = v) (h1 : 1 ≤ v)
    (h2 : v < 2) :
    FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0) + xa * xa * (xa * xa *
        hornerF (r0w.map Float.ofBits) (xa * xa) / hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)))
      (1 - v ^ 2 / 4 + v ^ 2 * (v ^ 2 * eval R0 (v ^ 2)) / eval S0 (v ^ 2)) (2227 / 1000 * 𝐮) := by
  have hu0 : (0 : ℝ) ≤ 𝐮 := by unfold unitRoundoff64; positivity
  rcases le_or_gt v (5 / 4) with c1 | c1
  · exact fmono (form2_0 xa hf hs he v hv h1 c1 h2) (mul_le_mul_of_nonneg_right (by norm_num) hu0)
  rcases le_or_gt v (3 / 2) with c2 | c2
  · exact fmono (form2_1 xa hf hs he v hv c1.le c2 h2) (mul_le_mul_of_nonneg_right (by norm_num) hu0)
  rcases le_or_gt v (7 / 4) with c3 | c3
  · exact fmono (form2_2 xa hf hs he v hv c2.le c3 h2) (mul_le_mul_of_nonneg_right (by norm_num) hu0)
  rcases le_or_gt v (15 / 8) with c4 | c4
  · exact fmono (form2_3 xa hf hs he v hv c3.le c4 h2) (mul_le_mul_of_nonneg_right (by norm_num) hu0)
  exact fmono (form2_4 xa hf hs he v hv c4.le h2.le h2) (mul_le_mul_of_nonneg_right (by norm_num) hu0)

/-- `j0` for `|x| < 2`. -/
theorem j0_small (x : Float) (hxf : Finite x.toBits)
    (h2 : x.toBits.toNat % 2 ^ 63 < 0x4000000000000000) :
    Finite (Bessel.j0 x).toBits ∧
      |value (Bessel.j0 x).toBits - J0 (value x.toBits)| ≤ 235 / 100 * 𝐮 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hab := F64Bits.toBits_abs x
  have hN := TrigSinCos.abs_toNat x.toBits
  have haf : Finite x.abs.toBits := by rw [hab]; exact TrigSinCos.abs_finite _ hxf
  have hav : value x.abs.toBits = |value x.toBits| := by rw [hab, TrigSinCos.abs_value]
  have haN : x.abs.toBits.toNat = x.toBits.toNat % 2 ^ 63 := by rw [hab, hN]
  have hs : Wasm.IEEE64.sign x.abs.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    rw [haN]; omega
  have hJ : J0 (value x.toBits) = J0 |value x.toBits| := by unfold J0; rw [sq_abs]
  rw [hJ, ← hav]
  set w := value x.abs.toBits with hw
  have hw0 : 0 ≤ w := by rw [hav]; exact abs_nonneg _
  have hw2 : w < 2 := by
    have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
      (right := (0x4000000000000000 : UInt64)) (by decide) (by rw [haN]; exact h2)
    rw [value_two] at h
    exact h
  have hixN := TrigSinCos.high_word x.toBits
  have hfin := TrigSinCos.finite_bound x.toBits hxf
  unfold Bessel.j0 Bessel.j0With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 1073741824) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  have hbig := huge_add x.abs haf (by rw [abs_of_nonneg hw0]; exact hw2.le)
  by_cases h13 : x.toBits >>> 32 &&& 2147483647 < 1059061760
  · rw [ite_eq_left (by simp [h13, hbig])]
    by_cases h27 : x.toBits >>> 32 &&& 2147483647 < 1044381696
    · rw [ite_eq_left h27, one_bits, value_one]
      refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
      have hsmall : w < 1 / 2 ^ 27 := by
        have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
          (right := (0x3E40000000000000 : UInt64)) (by decide) (by
            rw [haN]
            simp only [UInt64.reduceToNat]
            have := UInt64.lt_iff_toNat_lt.mp h27
            rw [hixN] at this
            simp only [UInt64.reduceToNat] at this
            omega)
        have e : value (0x3E40000000000000 : UInt64) = 1 / 2 ^ 27 := by
          rw [← ratOfWord_cast]
          have : ratOfWord 0x3E40000000000000 = 1 / 2 ^ 27 := by decide +kernel
          rw [this]; norm_num
        rw [e] at h
        exact h
      have hq := j0_quad w (by rw [abs_of_nonneg hw0]; linarith)
      have h2' : w ^ 2 ≤ 1 / 2 ^ 54 := by
        have := pow_le_pow_left₀ hw0 hsmall.le 2
        norm_num at this ⊢
        linarith
      have h4 : w ^ 4 ≤ 1 / 2 ^ 108 := by
        have := pow_le_pow_left₀ (by positivity) h2' 2
        rw [← pow_mul] at this
        norm_num at this ⊢
        linarith
      rw [abs_sub_comm]
      have := abs_sub_le (J0 w) (1 - w ^ 2 / 4) 1
      rw [show |1 - w ^ 2 / 4 - 1| = w ^ 2 / 4 by
        rw [show 1 - w ^ 2 / 4 - 1 = -(w ^ 2 / 4) by ring, abs_neg, abs_of_nonneg (by positivity)]]
        at this
      rw [hu]
      norm_num at hq h2' h4 ⊢
      linarith
    · rw [ite_eq_right h27]
      have hsmall : w < 1 / 2 ^ 13 := by
        have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
          (right := (0x3F20000000000000 : UInt64)) (by decide) (by
            rw [haN]
            simp only [UInt64.reduceToNat]
            have := UInt64.lt_iff_toNat_lt.mp h13
            rw [hixN] at this
            simp only [UInt64.reduceToNat] at this
            omega)
        have e : value (0x3F20000000000000 : UInt64) = 1 / 2 ^ 13 := by
          rw [← ratOfWord_cast]
          have : ratOfWord 0x3F20000000000000 = 1 / 2 ^ 13 := by decide +kernel
          rw [this]; norm_num
        rw [e] at h
        exact h
      have hz := sq_near x.abs haf (1 / 2 ^ 13) (by rw [abs_of_nonneg hw0]; exact hsmall.le)
        (by norm_num)
      have hfour : FApprox (4.0 : Float) 4 0 := by
        unfold FApprox Approx
        have hb4 : (4.0 : Float).toBits = 0x4010000000000000 := rfl
        rw [hb4, ← ratOfWord_cast]
        have : ratOfWord 0x4010000000000000 = 4 := by decide +kernel
        rw [this]
        exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num⟩
      have hw2' : |w ^ 2| ≤ 1 / 2 ^ 26 := by
        rw [abs_of_nonneg (by positivity)]
        have := pow_le_pow_left₀ hw0 hsmall.le 2
        norm_num at this ⊢
        linarith
      have hq := fapprox_div hz hfour (1 / 2 ^ 26) 4 hw2' (by norm_num) (by norm_num) _ le_rfl
        (by norm_num)
      have hres := fapprox_sub_half fapprox_one hq 1022 (by norm_num) (by
        have e : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
        rw [e]
        have : |1 - w ^ 2 / 4| ≤ 1 := by
          rw [abs_le]; constructor <;> nlinarith
        norm_num at this ⊢
        linarith)
      refine ⟨hres.1, ?_⟩
      have hq2 := j0_quad w (by rw [abs_of_nonneg hw0]; linarith)
      have h4 : w ^ 4 ≤ 1 / 2 ^ 52 := by
        have := pow_le_pow_left₀ (by positivity) (abs_le.mp hw2').2 2
        rw [abs_of_nonneg (by positivity)] at hw2'
        rw [← pow_mul] at this
        norm_num at this ⊢
        linarith
      have := abs_sub_le (value (1.0 - x.abs * x.abs / 4.0).toBits) (1 - w ^ 2 / 4) (J0 w)
      rw [abs_sub_comm (1 - w ^ 2 / 4)] at this
      have h3 := hres.2
      rw [hu]
      norm_num at h3 hq2 h4 ⊢
      linarith
  · rw [ite_eq_right (by simp [h13])]
    have h13' : 1 / 2 ^ 13 ≤ w := by
      have h := (F64PositiveOrder.value_le_iff (left := (0x3F20000000000000 : UInt64))
        (right := x.abs.toBits) (by decide) (by rw [haN]; omega)).mpr (by
          rw [haN]
          simp only [UInt64.reduceToNat]
          have : ¬ (1059061760 : UInt64).toNat > (x.toBits >>> 32 &&& 2147483647).toNat :=
            fun h => h13 (UInt64.lt_iff_toNat_lt.mpr h)
          rw [hixN] at this
          simp only [UInt64.reduceToNat] at this
          omega)
      have e : value (0x3F20000000000000 : UInt64) = 1 / 2 ^ 13 := by
        rw [← ratOfWord_cast]
        have : ratOfWord 0x3F20000000000000 = 1 / 2 ^ 13 := by decide +kernel
        rw [this]; norm_num
      rw [e] at h
      exact h
    have hap := j0_approx w (by rw [abs_of_nonneg hw0]; linarith)
    by_cases h1 : x.toBits >>> 32 &&& 2147483647 < 1072693248
    · rw [ite_eq_left h1]
      have hw1 : w ≤ 1 := by
        have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
          (right := (0x3FF0000000000000 : UInt64)) (by decide) (by
            rw [haN]
            simp only [UInt64.reduceToNat]
            have := UInt64.lt_iff_toNat_lt.mp h1
            rw [hixN] at this
            simp only [UInt64.reduceToNat] at this
            omega)
        rw [value_one] at h
        exact h.le
      have hf1 := form1 x.abs haf w hw.symm hw0 hw1
      refine ⟨hf1.1, ?_⟩
      show |value (1.0 + x.abs * x.abs * (x.abs * x.abs *
        hornerF (r0w.map Float.ofBits) (x.abs * x.abs) /
        hornerF (1.0 :: s0w.map Float.ofBits) (x.abs * x.abs) - 0.25)).toBits - J0 w| ≤ _
      have := abs_sub_le (value (1.0 + x.abs * x.abs * (x.abs * x.abs *
        hornerF (r0w.map Float.ofBits) (x.abs * x.abs) /
        hornerF (1.0 :: s0w.map Float.ofBits) (x.abs * x.abs) - 0.25)).toBits)
        (1 - w ^ 2 / 4 + w ^ 2 * (w ^ 2 * eval R0 (w ^ 2)) / eval S0 (w ^ 2)) (J0 w)
      rw [abs_sub_comm (1 - w ^ 2 / 4 + _)] at this
      have h3 := hf1.2
      rw [hu] at h3 hap ⊢
      norm_num at hap h3 ⊢
      linarith
    · rw [ite_eq_right h1]
      have hw1 : 1 ≤ w := by
        have h := (F64PositiveOrder.value_le_iff (left := (0x3FF0000000000000 : UInt64))
          (right := x.abs.toBits) (by decide) (by rw [haN]; omega)).mpr (by
            rw [haN]
            simp only [UInt64.reduceToNat]
            have : ¬ (1072693248 : UInt64).toNat > (x.toBits >>> 32 &&& 2147483647).toNat :=
              fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h)
            rw [hixN] at this
            simp only [UInt64.reduceToNat] at this
            omega)
        rw [value_one] at h
        exact h
      have he : 2 ≤ Wasm.IEEE64.exponent x.abs.toBits := by
        simp only [Wasm.IEEE64.exponent]
        rw [haN]
        have : ¬ (1072693248 : UInt64).toNat > (x.toBits >>> 32 &&& 2147483647).toNat :=
          fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h)
        rw [hixN] at this
        simp only [UInt64.reduceToNat] at this
        omega
      have hf2 := form2_all x.abs haf hs he w hw.symm hw1 hw2
      refine ⟨hf2.1, ?_⟩
      show |value ((1.0 + x.abs / 2.0) * (1.0 - x.abs / 2.0) + x.abs * x.abs *
        (x.abs * x.abs * hornerF (r0w.map Float.ofBits) (x.abs * x.abs) /
        hornerF (1.0 :: s0w.map Float.ofBits) (x.abs * x.abs))).toBits - J0 w| ≤ _
      have := abs_sub_le (value ((1.0 + x.abs / 2.0) * (1.0 - x.abs / 2.0) + x.abs * x.abs *
        (x.abs * x.abs * hornerF (r0w.map Float.ofBits) (x.abs * x.abs) /
        hornerF (1.0 :: s0w.map Float.ofBits) (x.abs * x.abs))).toBits)
        (1 - w ^ 2 / 4 + w ^ 2 * (w ^ 2 * eval R0 (w ^ 2)) / eval S0 (w ^ 2)) (J0 w)
      rw [abs_sub_comm (1 - w ^ 2 / 4 + _)] at this
      have h3 := hf2.2
      rw [hu] at h3 hap ⊢
      norm_num at hap h3 ⊢
      linarith

#print axioms form2_all
#print axioms j0_small

end Verified.Examples.BesselJ0Small
