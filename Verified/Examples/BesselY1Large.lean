import Verified.Examples.BesselY0Large

/-!
`Bessel.y1 x` for `x ≥ 2`: the result lies within `12 · 2^-53 · √(J₁(x)² + Y₁(x)²)` of `Y₁(x)`
(`y1_large`).  The proof is that of `BesselY0Large.y0_large` with `asym1`, the `P` and `Q` of
`BesselPQ1`, `θ = x - 3π/4`, and the constant 12.
-/

namespace Verified.Examples.BesselY1Large
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselPQRange BesselCombine
  BesselCase BesselCS BesselLarge BesselJ0Large BesselY0Large Real
open LeanExe.ProofKit.Bessel (J1 Y1)
open LeanExe.ProofKit.BesselPQ (P1 Q1 modulus1)

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

theorem sum_sq1 (w : ℝ) : (sin w - cos w) ^ 2 + (-sin w - cos w) ^ 2 = 2 := by
  linear_combination 2 * Real.sin_sq_add_cos_sq w

/-- `y1` for `x ≥ 2`. -/
theorem y1_large (x : Float) (hxf : Finite x.toBits) (hpos : x.toBits.toNat < 2 ^ 63)
    (h2 : 0x4000000000000000 ≤ x.toBits.toNat) :
    |value (Bessel.y1 x).toBits - Y1 (value x.toBits)| ≤
      12 * 𝐮 * √(J1 (value x.toBits) ^ 2 + Y1 (value x.toBits) ^ 2) := by
  obtain ⟨hw2, hwb⟩ := pos_facts x hxf hpos h2
  have hN : x.toBits.toNat % 2 ^ 63 = x.toBits.toNat := Nat.mod_eq_of_lt hpos
  have haf := hxf
  have haN : x.toBits.toNat = x.toBits.toNat % 2 ^ 63 := hN.symm
  have h2' : 0x4000000000000000 ≤ x.toBits.toNat % 2 ^ 63 := by rw [hN]; exact h2
  set w := value x.toBits with hwdef
  have hw0 : 0 < w := by linarith
  have hixN := TrigSinCos.high_word x.toBits
  have hfin := TrigSinCos.finite_bound x.toBits hxf
  have hM := fun (Pl : ℝ) (hPl0 : 0 < Pl) (hPl : Pl ≤ P1 w) =>
    modulus_ge (J := J1 w) (Y := Y1 w) (Q := Q1 w) hw0 hPl0 hPl (modulus1 w hw0)
  unfold Bessel.y1 Bessel.y1With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_right (show ¬ (x.toBits <<< 1 == 0) = true by
      rw [BesselSpecial.double_zero, decide_eq_true_iff]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 63 == 1) = true by
      rw [BesselSpecial.sign_bit, decide_eq_true_iff]; omega),
    ite_eq_left (show x.toBits >>> 32 &&& 2147483647 ≥ 1073741824 by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  by_cases hbig : x.toBits >>> 32 &&& 2147483647 > 1207959552
  · rw [ite_eq_left hbig]
    have hbig' : 0x4800000100000000 ≤ x.toBits.toNat % 2 ^ 63 := by
      have := UInt64.lt_iff_toNat_lt.mp hbig
      rw [hixN] at this
      simp only [UInt64.reduceToNat] at this
      omega
    have hw129 : 2 ^ 129 ≤ w := by
      have hlt : x.toBits.toNat < 2 ^ 63 := by rw [haN]; omega
      have h := (F64PositiveOrder.value_le_iff (left := (0x4800000000000000 : UInt64))
        (right := x.toBits) (by decide) hlt).mpr (by
          rw [haN]; simp only [UInt64.reduceToNat]; omega)
      rw [value_huge] at h
      exact h
    have hcc : FApprox (Bessel.asym1 Trig.invPi Trig.halfPi (x.toBits >>> 32 &&& 2147483647) x).2
        (-sin w - cos w) (627 / 100 * 𝐮) := by
      by_cases hlt : x.toBits >>> 32 &&& 2147483647 < 0x7fe00000
      · rcases asym1_near x haf hw2 _ rfl hlt with ⟨-, hc, -, -⟩ | ⟨-, hc, -, -⟩
        · exact hc
        · exact fmono hc (by norm_num [unitRoundoff64])
      · exact fmono (asym1_huge x haf _ hlt).2 (by norm_num [unitRoundoff64])
    obtain ⟨hP, hQ⟩ := huge_pq1 w hw129
    have hA : |sin w - cos w| ≤ 14143 / 10000 := abs_le_sqrt_two (by nlinarith [sum_sq1 w])
    have hB : |-sin w - cos w| ≤ 14143 / 10000 := abs_le_sqrt_two (by nlinarith [sum_sq1 w])
    have hTA : |(-sin w - cos w) - (P1 w * (-sin w - cos w) + Q1 w * (sin w - cos w))| ≤
        283 / 2 ^ 68 * (14143 / 10000) + 21 / 2 ^ 68 * (14143 / 10000) := by
      rw [show (-sin w - cos w) - (P1 w * (-sin w - cos w) + Q1 w * (sin w - cos w)) =
        -(P1 w - 1) * (-sin w - cos w) + -Q1 w * (sin w - cos w) by ring]
      have := abs_add_le (-(P1 w - 1) * (-sin w - cos w)) (-Q1 w * (sin w - cos w))
      rw [abs_mul, abs_mul, abs_neg, abs_neg] at this
      have e1 := mul_le_mul hP hB (abs_nonneg _) (by norm_num)
      have e2 := mul_le_mul hQ hA (abs_nonneg _) (by norm_num)
      linarith
    have hMT : |P1 w * (-sin w - cos w) + Q1 w * (sin w - cos w)| ≤
        (1 + 283 / 2 ^ 68) * (14143 / 10000) + 21 / 2 ^ 68 * (14143 / 10000) := by
      have hP' : |P1 w| ≤ 1 + 283 / 2 ^ 68 := by
        have := abs_sub_abs_le_abs_sub (P1 w) 1
        rw [abs_one] at this
        linarith
      have := abs_add_le (P1 w * (-sin w - cos w)) (Q1 w * (sin w - cos w))
      rw [abs_mul, abs_mul] at this
      have e1 := mul_le_mul hP' hB (abs_nonneg _) (by norm_num)
      have e2 := mul_le_mul hQ hA (abs_nonneg _) (by norm_num)
      linarith
    have hPl : 1 - 283 / 2 ^ 68 ≤ P1 w := by linarith [(abs_le.mp hP).1]
    have h := case_one (K := 12) hcc hTA hMT (by norm_num [unitRoundoff64])
      (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64]) (by norm_num) haf hw2 hwb
      (hM _ (by norm_num) hPl)
    rw [← Y1_form w hw0] at h
    exact h.2
  · rw [ite_eq_right hbig]
    have hsmall : x.toBits.toNat % 2 ^ 63 < 0x4800000100000000 := by
      have h' : ¬ (1207959552 : UInt64).toNat < (x.toBits >>> 32 &&& 2147483647).toNat :=
        fun h => hbig (UInt64.lt_iff_toNat_lt.mpr h)
      rw [hixN] at h'
      simp only [UInt64.reduceToNat] at h'
      omega
    have hlt : x.toBits >>> 32 &&& 2147483647 < 0x7fe00000 := by
      rw [UInt64.lt_iff_toNat_lt, hixN]; simp only [UInt64.reduceToNat]; omega
    have hbr := asym1_near x haf hw2 _ rfl hlt
    have hAB := sum_sq1 w
    by_cases r3 : x.toBits.toNat % 2 ^ 63 < 0x4006DB6D00000000
    · obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ1.pq_r3 x haf (by rw [haN]; exact h2')
        (by rw [haN]; exact r3)
      exact (large_add hp hq (by norm_num) hPl hPh hQh hbr hAB
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num) haf hw2 hwb (Y1_form w hw0) (hM _ (by norm_num) hPl)).2
    by_cases r2 : x.toBits.toNat % 2 ^ 63 < 0x40122E8B00000000
    · obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ1.pq_r2 x haf (by rw [haN]; omega)
        (by rw [haN]; exact r2)
      exact (large_add hp hq (by norm_num) hPl hPh hQh hbr hAB
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num) haf hw2 hwb (Y1_form w hw0) (hM _ (by norm_num) hPl)).2
    by_cases r1 : x.toBits.toNat % 2 ^ 63 < 0x4020000000000000
    · obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ1.pq_r1 x haf (by rw [haN]; omega)
        (by rw [haN]; exact r1)
      exact (large_add hp hq (by norm_num) hPl hPh hQh hbr hAB
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num) haf hw2 hwb (Y1_form w hw0) (hM _ (by norm_num) hPl)).2
    obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ1.pq_r0 x haf (by rw [haN]; omega)
      (by rw [haN]; exact hsmall)
    exact (large_add hp hq (by norm_num) hPl hPh hQh hbr hAB
      (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
      (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
      (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
      (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
      (by norm_num) haf hw2 hwb (Y1_form w hw0) (hM _ (by norm_num) hPl)).2

#print axioms sum_sq1
#print axioms y1_large

end Verified.Examples.BesselY1Large
