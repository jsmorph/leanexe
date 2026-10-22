import Library.Numerics.Float64.Bessel.BesselY1Large

/-!
`Bessel.j1 x` for `|x| ≥ 2`: the result lies within `12 · 2^-53 · √(J₁(|x|)² + Y₁(|x|)²)` of
`J₁(x)` (`j1_large`).  The code computes `z` from `|x|` as `BesselJ0Large.j0_large` does, with
`asym1`, the `P` and `Q` of `BesselPQ1`, and `θ = x - 3π/4`, and negates it when the sign bit of
`x` is set; `J₁` is odd, so `sign_select` carries the bound across the negation.
-/

namespace Library.Numerics.Float64.Bessel.BesselJ1Large
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselPQRange BesselCombine
  BesselCase BesselCS BesselLarge BesselJ0Large BesselY1Large Real
open LeanExe.ProofKit.Bessel (J1 Y1)
open LeanExe.ProofKit.BesselPQ (P1 Q1 modulus1)

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

theorem shr_sign (w : UInt64) : (w >>> 32 >>> 31 == 1) = decide (2 ^ 63 ≤ w.toNat) := by
  have h1 := Library.Numerics.Float64.Trig.TrigWords.shr_toNat (w >>> 32) 31
  have h2 := Library.Numerics.Float64.Trig.TrigWords.shr_toNat w 32
  have hw := w.toNat_lt
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt64.toNat_inj, h1, h2]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.reducePow] at hw ⊢
  omega

/-- The result or its negation, against `F` or `-F`. -/
theorem sign_select {T : Float} {F E : ℝ} (c : Bool) (h : Finite T.toBits ∧ |value T.toBits - F| ≤ E) :
    |value (if c = true then -T else T).toBits - (if c = true then -F else F)| ≤ E := by
  cases c
  · simpa using h.2
  · simp only [ite_true]
    have hn := fapprox_neg (fapprox_exact T h.1)
    have hv : value (-T).toBits = -value T.toBits := by
      have := hn.2
      rw [abs_nonpos_iff, sub_eq_zero] at this
      exact this
    rw [hv, show -value T.toBits - -F = -(value T.toBits - F) by ring, abs_neg]
    exact h.2

/-- `j1` for `|x| ≥ 2`. -/
theorem j1_large (x : Float) (hxf : Finite x.toBits)
    (h2 : 0x4000000000000000 ≤ x.toBits.toNat % 2 ^ 63) :
    |value (Bessel.j1 x).toBits - J1 (value x.toBits)| ≤
      12 * 𝐮 * √(J1 |value x.toBits| ^ 2 + Y1 |value x.toBits| ^ 2) := by
  obtain ⟨haf, haN, hav, hw2, hwb, hix⟩ := abs_facts x hxf h2
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x.toBits) with h | h
    · exfalso
      have : value x.toBits = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h]
        split <;> simp
      rw [this, abs_zero] at hav
      linarith
    · exact h
  have hsg : (x.toBits >>> 32 >>> 31 == 1) = true ↔ value x.toBits < 0 := by
    rw [shr_sign, decide_eq_true_iff, ← F64Magnitude.sign_value _ hmag]
    simp [Wasm.IEEE64.sign]
  have hJ : J1 (value x.toBits) = if (x.toBits >>> 32 >>> 31 == 1) = true
      then -J1 |value x.toBits| else J1 |value x.toBits| := by
    split_ifs with h
    · rw [abs_of_neg (hsg.mp h)]
      unfold J1
      rw [neg_sq]
      ring
    · rw [abs_of_nonneg (not_lt.mp fun h' => h (hsg.mpr h'))]
  rw [hJ, ← hav]
  set w := value x.abs.toBits with hwdef
  have hw0 : 0 < w := by linarith
  have hixN := Library.Numerics.Float64.Trig.TrigSinCos.high_word x.toBits
  have hfin := Library.Numerics.Float64.Trig.TrigSinCos.finite_bound x.toBits hxf
  have hM := fun (Pl : ℝ) (hPl0 : 0 < Pl) (hPl : Pl ≤ P1 w) =>
    modulus_ge (J := J1 w) (Y := Y1 w) (Q := Q1 w) hw0 hPl0 hPl (modulus1 w hw0)
  unfold Bessel.j1 Bessel.j1With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_left (show x.toBits >>> 32 &&& 2147483647 ≥ 1073741824 by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  apply sign_select
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
    have hcc : FApprox (Bessel.asym1 Trig.invPi Trig.halfPi (x.toBits >>> 32 &&& 2147483647) x.abs).1
        (sin w - cos w) (627 / 100 * 𝐮) := by
      by_cases hlt : x.toBits >>> 32 &&& 2147483647 < 0x7fe00000
      · rcases asym1_near x.abs haf hw2 _ hix.symm hlt with ⟨hc, -, -, -⟩ | ⟨hc, -, -, -⟩
        · exact fmono hc (by norm_num [unitRoundoff64])
        · exact hc
      · exact fmono (asym1_huge x.abs haf _ hlt).1 (by norm_num [unitRoundoff64])
    obtain ⟨hP, hQ⟩ := huge_pq1 w hw129
    have hA : |sin w - cos w| ≤ 14143 / 10000 := abs_le_sqrt_two (by nlinarith [sum_sq1 w])
    have hB : |-sin w - cos w| ≤ 14143 / 10000 := abs_le_sqrt_two (by nlinarith [sum_sq1 w])
    have hTA : |(sin w - cos w) - (P1 w * (sin w - cos w) - Q1 w * (-sin w - cos w))| ≤
        283 / 2 ^ 68 * (14143 / 10000) + 21 / 2 ^ 68 * (14143 / 10000) := by
      rw [show (sin w - cos w) - (P1 w * (sin w - cos w) - Q1 w * (-sin w - cos w)) =
        -(P1 w - 1) * (sin w - cos w) + Q1 w * (-sin w - cos w) by ring]
      have := abs_add_le (-(P1 w - 1) * (sin w - cos w)) (Q1 w * (-sin w - cos w))
      rw [abs_mul, abs_mul, abs_neg] at this
      have e1 := mul_le_mul hP hA (abs_nonneg _) (by norm_num)
      have e2 := mul_le_mul hQ hB (abs_nonneg _) (by norm_num)
      linarith
    have hMT : |P1 w * (sin w - cos w) - Q1 w * (-sin w - cos w)| ≤
        (1 + 283 / 2 ^ 68) * (14143 / 10000) + 21 / 2 ^ 68 * (14143 / 10000) := by
      have hP' : |P1 w| ≤ 1 + 283 / 2 ^ 68 := by
        have := abs_sub_abs_le_abs_sub (P1 w) 1
        rw [abs_one] at this
        linarith
      have := abs_sub (P1 w * (sin w - cos w)) (Q1 w * (-sin w - cos w))
      rw [abs_mul, abs_mul] at this
      have e1 := mul_le_mul hP' hA (abs_nonneg _) (by norm_num)
      have e2 := mul_le_mul hQ hB (abs_nonneg _) (by norm_num)
      linarith
    have hPl : 1 - 283 / 2 ^ 68 ≤ P1 w := by linarith [(abs_le.mp hP).1]
    have h := case_one (K := 12) hcc hTA hMT (by norm_num [unitRoundoff64])
      (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64]) (by norm_num) haf hw2 hwb
      (hM _ (by norm_num) hPl)
    rw [← J1_form w hw0] at h
    exact h
  · rw [ite_eq_right hbig]
    have hsmall : x.toBits.toNat % 2 ^ 63 < 0x4800000100000000 := by
      have h' : ¬ (1207959552 : UInt64).toNat < (x.toBits >>> 32 &&& 2147483647).toNat :=
        fun h => hbig (UInt64.lt_iff_toNat_lt.mpr h)
      rw [hixN] at h'
      simp only [UInt64.reduceToNat] at h'
      omega
    have hlt : x.toBits >>> 32 &&& 2147483647 < 0x7fe00000 := by
      rw [UInt64.lt_iff_toNat_lt, hixN]; simp only [UInt64.reduceToNat]; omega
    have hbr := asym1_near x.abs haf hw2 _ hix.symm hlt
    have hAB := sum_sq1 w
    by_cases r3 : x.toBits.toNat % 2 ^ 63 < 0x4006DB6D00000000
    · obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ1.pq_r3 x.abs haf (by rw [haN]; exact h2)
        (by rw [haN]; exact r3)
      exact (large_sub hp hq (by norm_num) hPl hPh hQh hbr hAB
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num) haf hw2 hwb (J1_form w hw0) (hM _ (by norm_num) hPl))
    by_cases r2 : x.toBits.toNat % 2 ^ 63 < 0x40122E8B00000000
    · obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ1.pq_r2 x.abs haf (by rw [haN]; omega)
        (by rw [haN]; exact r2)
      exact (large_sub hp hq (by norm_num) hPl hPh hQh hbr hAB
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num) haf hw2 hwb (J1_form w hw0) (hM _ (by norm_num) hPl))
    by_cases r1 : x.toBits.toNat % 2 ^ 63 < 0x4020000000000000
    · obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ1.pq_r1 x.abs haf (by rw [haN]; omega)
        (by rw [haN]; exact r1)
      exact (large_sub hp hq (by norm_num) hPl hPh hQh hbr hAB
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
        (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
        (by norm_num) haf hw2 hwb (J1_form w hw0) (hM _ (by norm_num) hPl))
    obtain ⟨hp, hq, hPl, hPh, hQh⟩ := BesselPQ1.pq_r0 x.abs haf (by rw [haN]; omega)
      (by rw [haN]; exact hsmall)
    exact (large_sub hp hq (by norm_num) hPl hPh hQh hbr hAB
      (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
      (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
      (by norm_num [unitRoundoff64]) (by norm_num [unitRoundoff64])
      (by norm_num [mulErr, unitRoundoff64]) (by norm_num [finErr, mulErr, Mis, eis, unitRoundoff64])
      (by norm_num) haf hw2 hwb (J1_form w hw0) (hM _ (by norm_num) hPl))

#print axioms shr_sign
#print axioms sign_select
#print axioms j1_large

end Library.Numerics.Float64.Bessel.BesselJ1Large
