import Library.Numerics.Float64.Bessel.BesselLarge

/-!
`Bessel.j0 x` for `|x| ≥ 2`: the result lies within `10 · 2^-53 · √(J₀(|x|)² + Y₀(|x|)²)` of
`J₀(x)` (`j0_large`).  The code works with `|x|`; on each of fdlibm's four ranges below `2 ^ 129`,
`BesselPQ0` gives `P` and `Q`, `BesselCS.asym0_near` the pair `(cc, ss)`, and
`BesselLarge.large_sub` the result, with the numeric conditions checked by `norm_num`.  From
`2 ^ 129` on the code drops `P - 1` and `Q`, which `BesselLarge.huge_pq0` bounds by `262 · 2^-68`
and `19 · 2^-68`.  `abs_facts` collects the facts about `|x|` that the four functions share.
-/

namespace Library.Numerics.Float64.Bessel.BesselJ0Large
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselPQRange BesselCombine
  BesselCase BesselCS BesselLarge Real
open LeanExe.ProofKit.Bessel (J0 Y0)
open LeanExe.ProofKit.BesselPQ (P0 Q0 modulus0)

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

theorem value_two : value (0x4000000000000000 : UInt64) = 2 := by
  rw [← ratOfWord_cast]
  have : ratOfWord 0x4000000000000000 = 2 := by decide +kernel
  rw [this]
  norm_num

theorem value_huge : value (0x4800000000000000 : UInt64) = 2 ^ 129 := by
  rw [← ratOfWord_cast]
  have : ratOfWord 0x4800000000000000 = 2 ^ 129 := by decide +kernel
  rw [this]
  norm_num

theorem value_top : value (0x7FF0000000000000 : UInt64) = 2 ^ 1024 := by
  rw [← ratOfWord_cast]
  have : ratOfWord 0x7FF0000000000000 = 2 ^ 1024 := by decide +kernel
  rw [this]
  norm_num

/-- `|x|` for `|x| ≥ 2`. -/
theorem abs_facts (x : Float) (hxf : Finite x.toBits)
    (h2 : 0x4000000000000000 ≤ x.toBits.toNat % 2 ^ 63) :
    Finite x.abs.toBits ∧ x.abs.toBits.toNat = x.toBits.toNat % 2 ^ 63 ∧
      value x.abs.toBits = |value x.toBits| ∧ 2 ≤ value x.abs.toBits ∧
      value x.abs.toBits ≤ 2 ^ 1024 ∧
      x.abs.toBits >>> 32 &&& (0x7fffffff : UInt64) = x.toBits >>> 32 &&& (0x7fffffff : UInt64) := by
  have hab := F64Bits.toBits_abs x
  have hN := Library.Numerics.Float64.Trig.TrigSinCos.abs_toNat x.toBits
  have hfin := Library.Numerics.Float64.Trig.TrigSinCos.finite_bound x.toBits hxf
  have hlt : x.abs.toBits.toNat < 2 ^ 63 := by rw [hab, hN]; omega
  refine ⟨by rw [hab]; exact Library.Numerics.Float64.Trig.TrigSinCos.abs_finite _ hxf, by rw [hab, hN],
    by rw [hab, Library.Numerics.Float64.Trig.TrigSinCos.abs_value], ?_, ?_, ?_⟩
  · have h := (F64PositiveOrder.value_le_iff (left := (0x4000000000000000 : UInt64))
      (right := x.abs.toBits) (by decide) hlt).mpr (by rw [hab, hN]; exact h2)
    rw [value_two] at h
    exact h
  · have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
      (right := (0x7FF0000000000000 : UInt64)) (by decide) (by rw [hab, hN]; exact hfin)
    rw [value_top] at h
    exact h.le
  · apply UInt64.toNat_inj.mp
    rw [Library.Numerics.Float64.Trig.TrigSinCos.high_word, Library.Numerics.Float64.Trig.TrigSinCos.high_word, hab, hN]
    omega

theorem sum_sq (w : ℝ) : (sin w + cos w) ^ 2 + (sin w - cos w) ^ 2 = 2 := by
  linear_combination 2 * Real.sin_sq_add_cos_sq w

/-- `j0` for `|x| ≥ 2`. -/
theorem j0_large (x : Float) (hxf : Finite x.toBits)
    (h2 : 0x4000000000000000 ≤ x.toBits.toNat % 2 ^ 63) :
    |value (Bessel.j0 x).toBits - J0 (value x.toBits)| ≤
      10 * 𝐮 * √(J0 |value x.toBits| ^ 2 + Y0 |value x.toBits| ^ 2) := by
  obtain ⟨haf, haN, hav, hw2, hwb, hix⟩ := abs_facts x hxf h2
  have hJ : J0 (value x.toBits) = J0 |value x.toBits| := by unfold J0; rw [sq_abs]
  rw [hJ, ← hav]
  set w := value x.abs.toBits with hwdef
  have hw0 : 0 < w := by linarith
  have hixN := Library.Numerics.Float64.Trig.TrigSinCos.high_word x.toBits
  have hfin := Library.Numerics.Float64.Trig.TrigSinCos.finite_bound x.toBits hxf
  have hM := fun (Pl : ℝ) (hPl0 : 0 < Pl) (hPl : Pl ≤ P0 w) =>
    modulus_ge (J := J0 w) (Y := Y0 w) (Q := Q0 w) hw0 hPl0 hPl (modulus0 w hw0)
  unfold Bessel.j0 Bessel.j0With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
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
      have hlt : x.abs.toBits.toNat < 2 ^ 63 := by rw [haN]; omega
      have h := (F64PositiveOrder.value_le_iff (left := (0x4800000000000000 : UInt64))
        (right := x.abs.toBits) (by decide) hlt).mpr (by
          rw [haN]; simp only [UInt64.reduceToNat]; omega)
      rw [value_huge] at h
      exact h
    have hcc : FApprox (Bessel.asym0 Trig.invPi Trig.halfPi (x.toBits >>> 32 &&& 2147483647) x.abs).1
        (sin w + cos w) (627 / 100 * 𝐮) := by
      by_cases hlt : x.toBits >>> 32 &&& 2147483647 < 0x7fe00000
      · rcases asym0_near x.abs haf hw2 _ hix.symm hlt with ⟨hc, -, -, -⟩ | ⟨hc, -, -, -⟩
        · exact fmono hc (by norm_num [unitRoundoff64])
        · exact hc
      · exact fmono (asym0_huge x.abs haf _ hlt).1 (by norm_num [unitRoundoff64])
    obtain ⟨hP, hQ⟩ := huge_pq0 w hw129
    have hA : |sin w + cos w| ≤ 14143 / 10000 := abs_le_sqrt_two (by nlinarith [sum_sq w])
    have hB : |sin w - cos w| ≤ 14143 / 10000 := abs_le_sqrt_two (by nlinarith [sum_sq w])
    have hTA : |(sin w + cos w) - (P0 w * (sin w + cos w) - Q0 w * (sin w - cos w))| ≤
        262 / 2 ^ 68 * (14143 / 10000) + 19 / 2 ^ 68 * (14143 / 10000) := by
      rw [show (sin w + cos w) - (P0 w * (sin w + cos w) - Q0 w * (sin w - cos w)) =
        -(P0 w - 1) * (sin w + cos w) + Q0 w * (sin w - cos w) by ring]
      have := abs_add_le (-(P0 w - 1) * (sin w + cos w)) (Q0 w * (sin w - cos w))
      rw [abs_mul, abs_mul, abs_neg] at this
      have e1 := mul_le_mul hP hA (abs_nonneg _) (by norm_num)
      have e2 := mul_le_mul hQ hB (abs_nonneg _) (by norm_num)
      linarith
    have hMT : |P0 w * (sin w + cos w) - Q0 w * (sin w - cos w)| ≤
        (1 + 262 / 2 ^ 68) * (14143 / 10000) + 19 / 2 ^ 68 * (14143 / 10000) := by
      have hP' : |P0 w| ≤ 1 + 262 / 2 ^ 68 := by
        have := abs_sub_abs_le_abs_sub (P0 w) 1
        rw [abs_one] at this
        linarith
      have := abs_sub (P0 w * (sin w + cos w)) (Q0 w * (sin w - cos w))
      rw [abs_mul, abs_mul] at this
      have e1 := mul_le_mul hP' hA (abs_nonneg _) (by norm_num)
      have e2 := mul_le_mul hQ hB (abs_nonneg _) (by norm_num)
      linarith
    have hPl : 1 - 262 / 2 ^ 68 ≤ P0 w := by linarith [(abs_le.mp hP).1]
    have h := case_one (K := 10) hcc hTA hMT (by norm_num [unitRoundoff64])
      (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64]) (by norm_num) haf hw2 hwb
      (hM _ (by norm_num) hPl)
    rw [← J0_form w hw0] at h
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
    have hbr := asym0_near x.abs haf hw2 _ hix.symm hlt
    have hAB := sum_sq w
    by_cases r3 : x.toBits.toNat % 2 ^ 63 < 0x4006DB6D00000000
    · obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ0.pq_r3 x.abs haf (by rw [haN]; exact h2)
        (by rw [haN]; exact r3)
      exact (large_sub hp hq (by norm_num) hPl hPh hQh hbr hAB
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num) haf hw2 hwb (J0_form w hw0) (hM _ (by norm_num) hPl)).2
    by_cases r2 : x.toBits.toNat % 2 ^ 63 < 0x40122E8B00000000
    · obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ0.pq_r2 x.abs haf (by rw [haN]; omega)
        (by rw [haN]; exact r2)
      exact (large_sub hp hq (by norm_num) hPl hPh hQh hbr hAB
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num) haf hw2 hwb (J0_form w hw0) (hM _ (by norm_num) hPl)).2
    by_cases r1 : x.toBits.toNat % 2 ^ 63 < 0x4020000000000000
    · obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ0.pq_r1 x.abs haf (by rw [haN]; omega)
        (by rw [haN]; exact r1)
      exact (large_sub hp hq (by norm_num) hPl hPh hQh hbr hAB
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num) haf hw2 hwb (J0_form w hw0) (hM _ (by norm_num) hPl)).2
    obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ0.pq_r0 x.abs haf (by rw [haN]; omega)
      (by rw [haN]; exact hsmall)
    exact (large_sub hp hq (by norm_num) hPl hPh hQh hbr hAB
      (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
      (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
      (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
      (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
      (by norm_num) haf hw2 hwb (J0_form w hw0) (hM _ (by norm_num) hPl)).2

#print axioms abs_facts
#print axioms j0_large

end Library.Numerics.Float64.Bessel.BesselJ0Large
