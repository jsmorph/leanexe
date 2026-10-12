import Verified.Examples.AcosTheoremNeg
import LeanExe.ProofKit.F64RoundDouble

/-!
`Asin.acos x` for `1/2 ≤ x < 1`: `2 (df + (r s + c))` with the exact `z = (1 - x)/2`, `s = √z`,
`df` the high part of `s`, `c = (z - df²)/(s + df)`, and `r = asinRatio z`, against
`arccos x = 2 arcsin √z`.  The result reaches down to `2 ^ -26`, so every bound is relative to
`s₀ = √z`: `df + c` lies within `2 ^ -70 s₀` of `s₀`, the sum `df + w` rounds to a nearest word
of its exact value, the doubling is exact and keeps that word nearest (`F64RoundDouble`), and
`F64RoundNearest.within_one_of_rounded_rel` finishes with `ρ = 0.7 · 2 ^ -53`.
-/

namespace Verified.Examples.AcosTheoremPos
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest PolyBound AsinTheoremSupport
  AsinTheoremRatio AsinTheoremBranches AsinTheoremSmall AcosTheoremBranches

set_option exponentiation.threshold 4096

set_option maxHeartbeats 4000000 in
theorem pos_core (x : Float) (hx : Finite x.toBits) (h1 : 1 / 2 ≤ value x.toBits)
    (h2 : value x.toBits < 1) (T0 Mr er : ℝ) (hT0 : T0 ≤ 1 / 4)
    (hzT : (1 - value x.toBits) / 2 ≤ T0)
    (hr : FSApprox (Asin.asinRatio ((1.0 - x) * 0.5))
      ((1 - value x.toBits) / 2 * eval AsinKernelPoly.asinP ((1 - value x.toBits) / 2) /
        eval AsinKernelPoly.asinQ ((1 - value x.toBits) / 2)) ((1 - value x.toBits) / 2) Mr er)
    (hbud : (er * 2 ^ 53 * (101 / 100) + (Mr + er) * (101 / 100) + Mr + Mr * (101 / 100) +
      11 / 128) * T0 + 1 / 100 ≤ 7 / 10) :
    F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits))
      (posTail ((1.0 - x) * 0.5)).toBits := by
  obtain ⟨hzf, hzv, hz0⟩ := pos_z_exact x hx h1 h2
  have hy := AsinTheoremHalf.arccos_half (value x.toBits) (by linarith) (by linarith)
  have hMr := hr.M_nonneg
  have her := hr.e_nonneg
  unfold posTail
  set v := value x.toBits with hv
  set z := (1.0 - x) * 0.5 with hzdef
  set vz := (1 - v) / 2 with hvz
  have hvzp : 0 < vz := lt_of_lt_of_le (by positivity) hz0
  have hvz4 : vz ≤ 1 / 4 := hzT.trans hT0
  have hT0p : 0 ≤ T0 := le_trans hvzp.le hzT
  have hMT0 := mul_nonneg hMr hT0p
  have heT0 := mul_nonneg her hT0p
  have hMT : Mr * T0 ≤ 7 / 10 := by nlinarith
  have heT : er * T0 ≤ 1 / 2 ^ 53 := by nlinarith
  obtain ⟨hrA, hrM⟩ := Log1pTheoremTail.fsapprox_abs hr (le_refl vz)
  set R := vz * eval AsinKernelPoly.asinP vz / eval AsinKernelPoly.asinQ vz with hR
  have hRT : |R| ≤ Mr * T0 := hrM.trans (mul_le_mul_of_nonneg_left hzT hMr)
  -- `s = √z`, with `s₀ = √z` exact
  have hzA : FApprox z vz 0 := ⟨hzf, by rw [hzv, sub_self, abs_zero]⟩
  have hs := Approx.mono (fapprox_sqrt hzA vz vz hvzp le_rfl hvzp le_rfl (Real.sqrt vz)
    (by rw [add_zero])) (e' := Real.sqrt vz / 2 ^ 53) (by rw [zero_div, zero_add])
  have hs0p : 0 < Real.sqrt vz := Real.sqrt_pos.mpr hvzp
  have hss : Real.sqrt vz * Real.sqrt vz = vz := Real.mul_self_sqrt hvzp.le
  have hs02 : Real.sqrt vz ≤ 1 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
    linarith
  have hs027 : 1 / 2 ^ 27 ≤ Real.sqrt vz := by
    rw [Real.le_sqrt (by positivity) hvzp.le]
    norm_num
    linarith
  have hker := asin_kernel (Real.sqrt vz) (by rw [abs_of_pos hs0p]; linarith)
  rw [hss, abs_of_pos hs0p, ← hR] at hker
  have harc := abs_le_abs_arcsin (Real.sqrt vz) (by rw [abs_of_pos hs0p]; linarith)
  rw [abs_of_pos hs0p, abs_of_nonneg (Real.arcsin_nonneg.mpr hs0p.le)] at harc
  set s0 := Real.sqrt vz with hs0
  have hs0n : 0 ≤ s0 := hs0p.le
  have hsd53 : 0 ≤ s0 / 2 ^ 53 := div_nonneg hs0n (by norm_num)
  set s := z.sqrt with hsd
  set vs := value s.toBits with hvs
  obtain ⟨hes1, hes2⟩ := abs_le.mp hs.2
  have hvs0 : 0 < vs := by
    have : s0 / 2 ^ 53 < s0 := div_lt_self hs0p (by norm_num)
    linarith
  -- `df`, the high part of `s`
  have hse : 506 ≤ Wasm.IEEE64.exponent s.toBits :=
    Log1pTheoremCorr.exponent_ge _ 506 (-517) (by norm_num) (by norm_num) (by
      rw [abs_of_pos hvs0, show (2 : ℝ) ^ (-517 : ℤ) = 1 / 2 ^ 517 by norm_num]
      have h3 : (1 : ℝ) / 2 ^ 517 ≤ 1 / 2 ^ 27 - 1 / 2 ^ 27 / 2 ^ 53 := by norm_num
      linarith)
  obtain ⟨hwf, hwle, hwd, q, hq, hqm⟩ := trunc_facts s.toBits hvs0 hs.1 hse
  have hwb : (wOf s).toBits = s.toBits &&& 0xFFFFFFFF00000000 := by
    unfold wOf
    rw [F64Bits.toBits_ofBits, not_nan_of_finite hwf]
    simp only [Bool.false_eq_true, ite_false]
  rw [← hwb] at hwf hwle hwd hqm
  set w := wOf s with hwdef
  set vw := value w.toBits with hvw
  have hvw0 : 0 < vw := by
    have : vs / 2 ^ 20 < vs := div_lt_self hvs0 (by norm_num)
    linarith
  have hvwl : (1 - 1 / 2 ^ 53) * (1 - 1 / 2 ^ 20) * s0 ≤ vw := by linarith
  have hvwh : vw ≤ (1 + 1 / 2 ^ 53) * s0 := by linarith
  have hk0 : 0 ≤ (1 + 1 / 2 ^ 53) * s0 := mul_nonneg (by norm_num) hs0n
  -- `w * w` and `z - w * w` are exact
  have hww := F64ExactProduct.mul_exact_scaled w.toBits w.toBits hwf hwf q q
    (Wasm.IEEE64.exponent s.toBits - 1 + 32) (Wasm.IEEE64.exponent s.toBits - 1 + 32) hqm hqm
    (lt_of_le_of_lt (Nat.mul_le_mul hq.le hq.le) (by norm_num)) (by omega) (by
      have := exponent_lt_one s.toBits (by
        rw [abs_of_pos hvs0]
        have : (1 + 1 / 2 ^ 53 : ℝ) * (1 / 2) < 1 := by norm_num
        linarith)
      omega)
  rw [← F64Bits.toBits_mul] at hww
  have hwwv : value (w * w).toBits = vw * vw := hww.2.1
  have hwwf := hww.1
  clear hww hqm
  have hww2 : vw * vw ≤ (1 + 1 / 2 ^ 53) ^ 2 * vz := by
    have := mul_le_mul hvwh hvwh hvw0.le hk0
    rw [← hss]
    linarith
  have hww1 : (1 - 1 / 2 ^ 53) ^ 2 * (1 - 1 / 2 ^ 20) ^ 2 * vz ≤ vw * vw := by
    have hl0 : 0 ≤ (1 - 1 / 2 ^ 53) * (1 - 1 / 2 ^ 20) * s0 := mul_nonneg (by norm_num) hs0n
    have := mul_le_mul hvwl hvwl hl0 hvw0.le
    rw [← hss]
    linarith
  have hc2 : (1 + 1 / 2 ^ 53 : ℝ) ^ 2 ≤ 2 := by norm_num
  have hc1 : (1 / 2 : ℝ) ≤ (1 - 1 / 2 ^ 53) ^ 2 * (1 - 1 / 2 ^ 20) ^ 2 := by norm_num
  have htw := F64Exact.sub_exact z.toBits (w * w).toBits hzf hwwf (by rw [hzv]; exact hvzp)
    (by rw [hwwv]; exact mul_pos hvw0 hvw0) (by rw [hwwv, hzv]; nlinarith)
    (by rw [hwwv, hzv]; nlinarith) (by rw [hzv]; linarith [(by norm_num : (1 / 4 : ℝ) < 2 ^ 900)])
    (by rw [hwwv]; nlinarith [(by norm_num : (1 : ℝ) < 2 ^ 900)])
  rw [← F64Bits.toBits_sub, hzv, hwwv] at htw
  have htwA : FApprox (z - w * w) (vz - vw * vw) 0 := ⟨htw.1, by rw [htw.2, sub_self, abs_zero]⟩
  have htw0 : |vz - vw * vw| ≤ 1 / 2 ^ 18 * vz := by
    have h3 : (1 : ℝ) - (1 - 1 / 2 ^ 53) ^ 2 * (1 - 1 / 2 ^ 20) ^ 2 ≤ 1 / 2 ^ 18 := by norm_num
    have h4 : (1 + 1 / 2 ^ 53 : ℝ) ^ 2 - 1 ≤ 1 / 2 ^ 18 := by norm_num
    rw [abs_le]
    constructor <;> nlinarith
  -- `s + w`
  have hsw := fapprox_add (approx_self s.toBits hs.1) (approx_self w.toBits hwf)
    (2 * (1 + 1 / 2 ^ 53) * s0) (by rw [abs_of_pos (by linarith)]; linarith) (by linarith)
  set EB := 0 + 0 + 2 * (1 + 1 / 2 ^ 53) * s0 / 2 ^ 53 with hEBd
  have hEB0 : 0 ≤ EB := by rw [hEBd]; linarith
  have hEB : EB ≤ 3 / 2 ^ 53 * s0 := by
    have h3 : EB = (2 * (1 + 1 / 2 ^ 53) / 2 ^ 53) * s0 := by rw [hEBd]; ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right (by norm_num) hs0n
  have hsw0 : 19 / 10 * s0 ≤ |vs + vw| := by
    rw [abs_of_pos (by linarith)]
    linarith
  -- `c`
  have hden : 18 / 10 * s0 ≤ 19 / 10 * s0 - EB := by
    have : (3 : ℝ) / 2 ^ 53 * s0 ≤ 1 / 10 * s0 := mul_le_mul_of_nonneg_right (by norm_num) hs0n
    linarith
  have hdenp : 0 < 19 / 10 * s0 - EB := by
    have : 0 < 18 / 10 * s0 := mul_pos (by norm_num) hs0p
    linarith
  have hKs : 0 ≤ 1 / 2 ^ 18 * s0 := mul_nonneg (by norm_num) hs0n
  have hc := fapprox_div htwA hsw (1 / 2 ^ 18 * vz) (19 / 10 * s0) htw0 hsw0
    (by
      have : (3 : ℝ) / 2 ^ 53 * s0 < 19 / 10 * s0 := mul_lt_mul_of_pos_right (by norm_num) hs0p
      linarith)
    (1 / 2 ^ 18 * s0) (by
      rw [div_le_iff₀ hdenp, add_zero, ← hss]
      have h3 : 1 / 2 ^ 18 * s0 * (18 / 10 * s0) ≤ 1 / 2 ^ 18 * s0 * (19 / 10 * s0 - EB) :=
        mul_le_mul_of_nonneg_left hden hKs
      nlinarith [mul_self_nonneg s0])
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 18 * (1 / 2) < 2 ^ 1022)])
  have hcA := Approx.mono hc (e' := s0 / 2 ^ 69) (by
    have ht1 : (0 + 1 / 2 ^ 18 * vz * EB / (19 / 10 * s0)) / (19 / 10 * s0 - EB) ≤
        s0 / 2 ^ 70 := by
      rw [zero_add, div_div, div_le_iff₀ (mul_pos (mul_pos (by norm_num) hs0p) hdenp), ← hss]
      have h3 : 1 / 2 ^ 18 * (s0 * s0) * EB ≤ 1 / 2 ^ 18 * (s0 * s0) * (3 / 2 ^ 53 * s0) :=
        mul_le_mul_of_nonneg_left hEB (mul_nonneg (by norm_num) (mul_self_nonneg s0))
      have h4 : s0 / 2 ^ 70 * (19 / 10 * s0 * (18 / 10 * s0)) ≤
          s0 / 2 ^ 70 * (19 / 10 * s0 * (19 / 10 * s0 - EB)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hden (mul_nonneg (by norm_num) hs0n))
          (div_nonneg hs0n (by norm_num))
      have h5 : 0 ≤ s0 * s0 * s0 := mul_nonneg (mul_self_nonneg s0) hs0n
      nlinarith
    have ht3 : (1 : ℝ) / 2 ^ 1075 ≤ s0 / 2 ^ 1000 := by
      have : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 27 / 2 ^ 1000 := by norm_num
      have h4 : 1 / 2 ^ 27 / 2 ^ 1000 ≤ s0 / 2 ^ 1000 :=
        div_le_div_of_nonneg_right hs027 (by norm_num)
      linarith
    have ht2 : 1 / 2 ^ 18 * s0 / 2 ^ 53 = s0 / 2 ^ 71 := by ring
    have h5 : s0 / 2 ^ 70 + s0 / 2 ^ 71 + s0 / 2 ^ 1000 ≤ s0 / 2 ^ 69 := by
      have h6 : (1 / 2 ^ 70 + 1 / 2 ^ 71 + 1 / 2 ^ 1000 : ℝ) ≤ 1 / 2 ^ 69 := by norm_num
      have h7 := mul_le_mul_of_nonneg_left h6 hs0n
      have h8 : s0 * (1 / 2 ^ 70 + 1 / 2 ^ 71 + 1 / 2 ^ 1000) =
          s0 / 2 ^ 70 + s0 / 2 ^ 71 + s0 / 2 ^ 1000 := by ring
      have h9 : s0 * (1 / 2 ^ 69) = s0 / 2 ^ 69 := by ring
      linarith
    rw [ht2]
    linarith)
  set c := (z - w * w) / (s + w) with hcd
  set vc := (vz - vw * vw) / (vs + vw) with hvc
  have hvcM : |vc| ≤ 1 / 2 ^ 18 * s0 := by
    rw [hvc, abs_div, div_le_iff₀ (by linarith)]
    have h3 : 1 / 2 ^ 18 * s0 * (19 / 10 * s0) ≤ 1 / 2 ^ 18 * s0 * |vs + vw| :=
      mul_le_mul_of_nonneg_left hsw0 hKs
    nlinarith [mul_self_nonneg s0]
  -- `w + c` against `s₀`
  have hdc : |vw + vc - s0| ≤ s0 / 2 ^ 70 := by
    have hsum : 0 < vs + vw := by linarith
    have hne : vs + vw ≠ 0 := hsum.ne'
    have heq : vw + vc - s0 = (s0 - vw) * (s0 - vs) / (vs + vw) := by
      rw [hvc, ← hss]
      field_simp
      ring
    rw [heq, abs_div, abs_mul, abs_of_pos hsum, div_le_iff₀ hsum]
    have h3 : |s0 - vw| ≤ (1 / 2 ^ 20 + 1 / 2 ^ 53) * s0 := by
      rw [abs_le]
      constructor <;> nlinarith
    have h4 : |s0 - vs| ≤ s0 / 2 ^ 53 := by
      rw [abs_sub_comm]
      exact hs.2
    have h5 := mul_le_mul h3 h4 (abs_nonneg _) (mul_nonneg (by norm_num) hs0n)
    have h6 : (1 / 2 ^ 20 + 1 / 2 ^ 53) * s0 * (s0 / 2 ^ 53) ≤ s0 / 2 ^ 70 * (19 / 10 * s0) := by
      have hc : (1 / 2 ^ 20 + 1 / 2 ^ 53 : ℝ) / 2 ^ 53 ≤ 1 / 2 ^ 70 * (19 / 10) := by norm_num
      calc (1 / 2 ^ 20 + 1 / 2 ^ 53) * s0 * (s0 / 2 ^ 53) =
            ((1 / 2 ^ 20 + 1 / 2 ^ 53) / 2 ^ 53) * (s0 * s0) := by ring
        _ ≤ (1 / 2 ^ 70 * (19 / 10)) * (s0 * s0) :=
            mul_le_mul_of_nonneg_right hc (mul_self_nonneg s0)
        _ = s0 / 2 ^ 70 * (19 / 10 * s0) := by ring
    have h7 : s0 / 2 ^ 70 * (19 / 10 * s0) ≤ s0 / 2 ^ 70 * (vs + vw) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hs0n (by norm_num))
    exact h5.trans (h6.trans h7)
  -- `r s`
  have hvsM : |vs| ≤ (1 + 1 / 2 ^ 53) * s0 := by rw [abs_of_pos hvs0]; linarith
  have hrs := Approx.mono (fapprox_mul hrA (approx_self s.toBits hs.1) (Mr * vz)
    ((1 + 1 / 2 ^ 53) * s0) hrM hvsM ((Mr * vz + er * vz) * ((1 + 1 / 2 ^ 53) * s0))
    (by rw [add_zero]) (by
      have h3 : Mr * vz + er * vz ≤ 1 := by nlinarith
      have h4 : (1 + 1 / 2 ^ 53) * s0 ≤ 1 := by linarith
      have h5 : 0 ≤ Mr * vz + er * vz := by nlinarith
      have h6 := mul_le_mul h3 h4 hk0 (by norm_num)
      linarith [(by norm_num : (1 : ℝ) * 1 < 2 ^ 1022)]))
    (e' := (er * 2 ^ 53 * (101 / 100) + (Mr + er) * (101 / 100)) * T0 * (s0 / 2 ^ 53) +
      s0 / 2 ^ 1000) (by
      have h3 : (1 : ℝ) / 2 ^ 1075 ≤ s0 / 2 ^ 1000 := by
        have : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 27 / 2 ^ 1000 := by norm_num
        have h4 : 1 / 2 ^ 27 / 2 ^ 1000 ≤ s0 / 2 ^ 1000 :=
          div_le_div_of_nonneg_right hs027 (by norm_num)
        linarith
      have h4 : (1 + 1 / 2 ^ 53 : ℝ) ≤ 101 / 100 := by norm_num
      have h5 : er * vz * ((1 + 1 / 2 ^ 53) * s0) ≤
          er * 2 ^ 53 * (101 / 100) * T0 * (s0 / 2 ^ 53) := by
        have h6 : er * vz * ((1 + 1 / 2 ^ 53) * s0) ≤ er * T0 * ((101 / 100) * s0) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hzT her) (mul_le_mul_of_nonneg_right h4 hs0n)
            hk0 heT0
        have h7 : er * T0 * ((101 / 100) * s0) =
            er * 2 ^ 53 * (101 / 100) * T0 * (s0 / 2 ^ 53) := by ring
        linarith
      have h6 : (Mr * vz + er * vz) * ((1 + 1 / 2 ^ 53) * s0) / 2 ^ 53 ≤
          (Mr + er) * (101 / 100) * T0 * (s0 / 2 ^ 53) := by
        have h7 : (Mr * vz + er * vz) * ((1 + 1 / 2 ^ 53) * s0) ≤
            (Mr + er) * T0 * ((101 / 100) * s0) := by
          rw [show Mr * vz + er * vz = (Mr + er) * vz by ring]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hzT (by linarith))
            (mul_le_mul_of_nonneg_right h4 hs0n) hk0 (by nlinarith)
        have h8 : (Mr + er) * T0 * ((101 / 100) * s0) / 2 ^ 53 =
            (Mr + er) * (101 / 100) * T0 * (s0 / 2 ^ 53) := by ring
        have h9 := div_le_div_of_nonneg_right h7 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
        linarith
      linarith)
  -- `w₂ = r s + c`
  have hRvs : |R * vs| ≤ Mr * T0 * (101 / 100) * s0 := by
    rw [abs_mul]
    have h4 : |vs| ≤ (101 / 100) * s0 :=
      hvsM.trans (mul_le_mul_of_nonneg_right (by norm_num) hs0n)
    have := mul_le_mul hRT h4 (abs_nonneg _) hMT0
    linarith
  have hA7 : (er * 2 ^ 53 * (101 / 100) + (Mr + er) * (101 / 100)) * T0 * (s0 / 2 ^ 53) ≤
      7 / 10 * (s0 / 2 ^ 53) := by
    have h5 : (er * 2 ^ 53 * (101 / 100) + (Mr + er) * (101 / 100)) * T0 ≤ 7 / 10 := by nlinarith
    exact mul_le_mul_of_nonneg_right h5 hsd53
  have hw2 := fapprox_add hrs hcA ((Mr * T0 * (101 / 100) + 1 / 2 ^ 16) * s0) (by
    have h3 := abs_add_le (R * vs) vc
    have h7 : 7 / 10 * (s0 / 2 ^ 53) + s0 / 2 ^ 1000 + s0 / 2 ^ 69 ≤ s0 / 2 ^ 18 := by
      have h8 : (7 / 10 / 2 ^ 53 + 1 / 2 ^ 1000 + 1 / 2 ^ 69 : ℝ) ≤ 1 / 2 ^ 18 := by norm_num
      have h9 := mul_le_mul_of_nonneg_left h8 hs0n
      have h10 : s0 * (7 / 10 / 2 ^ 53 + 1 / 2 ^ 1000 + 1 / 2 ^ 69) =
          7 / 10 * (s0 / 2 ^ 53) + s0 / 2 ^ 1000 + s0 / 2 ^ 69 := by ring
      have h11 : s0 * (1 / 2 ^ 18) = s0 / 2 ^ 18 := by ring
      linarith
    have h5 : 1 / 2 ^ 18 * s0 + s0 / 2 ^ 18 ≤ 1 / 2 ^ 16 * s0 := by linarith
    nlinarith) (by
      have h3 : (Mr * T0 * (101 / 100) + 1 / 2 ^ 16) * s0 ≤ Mr * T0 * (101 / 100) + 1 / 2 ^ 16 := by
        have h4 : 0 ≤ Mr * T0 * (101 / 100) + 1 / 2 ^ 16 := by linarith
        nlinarith
      linarith)
  set w2 := Asin.asinRatio z * s + c with hw2d
  set vw2 := value w2.toBits with hvw2
  -- the exact sum `w + w₂` against `arcsin s₀`
  have hS : |vw + vw2 - Real.arcsin s0| ≤ 7 / 10 / 2 ^ 53 * s0 := by
    have hw2e := hw2.2
    have heq : vw + vw2 - Real.arcsin s0 = (vw2 - (R * vs + vc)) + (vw + vc - s0) +
        R * (vs - s0) + (s0 + s0 * R - Real.arcsin s0) := by ring
    rw [heq]
    have h3 := abs_add_le ((vw2 - (R * vs + vc)) + (vw + vc - s0) + R * (vs - s0))
      (s0 + s0 * R - Real.arcsin s0)
    have h4 := abs_add_le ((vw2 - (R * vs + vc)) + (vw + vc - s0)) (R * (vs - s0))
    have h5 := abs_add_le (vw2 - (R * vs + vc)) (vw + vc - s0)
    have h6 : |R * (vs - s0)| ≤ Mr * T0 * (s0 / 2 ^ 53) := by
      rw [abs_mul]
      exact mul_le_mul hRT hs.2 (abs_nonneg _) hMT0
    have h7 : |s0 + s0 * R - Real.arcsin s0| ≤ T0 * (11 / 128) * (s0 / 2 ^ 53) := by
      rw [abs_sub_comm]
      refine hker.trans ?_
      have h8 : s0 ^ 3 = vz * s0 := by rw [← hss]; ring
      rw [h8]
      have h9 : vz * s0 * ((11 / 16) / 2 ^ 56) ≤ T0 * s0 * ((11 / 16) / 2 ^ 56) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hzT hs0n) (by norm_num)
      have h10 : T0 * s0 * ((11 / 16) / 2 ^ 56) = T0 * (11 / 128) * (s0 / 2 ^ 53) := by ring
      linarith
    have h9 : (er * 2 ^ 53 * (101 / 100) + (Mr + er) * (101 / 100)) * T0 * (s0 / 2 ^ 53) +
        s0 / 2 ^ 1000 + s0 / 2 ^ 69 + (Mr * T0 * (101 / 100) + 1 / 2 ^ 16) * s0 / 2 ^ 53 +
          s0 / 2 ^ 70 + Mr * T0 * (s0 / 2 ^ 53) + T0 * (11 / 128) * (s0 / 2 ^ 53) =
        ((er * 2 ^ 53 * (101 / 100) + (Mr + er) * (101 / 100) + Mr + Mr * (101 / 100) +
          11 / 128) * T0 + (2 ^ 53 / 2 ^ 1000 + 2 ^ 53 / 2 ^ 69 + 1 / 2 ^ 16 +
            2 ^ 53 / 2 ^ 70)) * (s0 / 2 ^ 53) := by ring
    have h10 : (2 ^ 53 / 2 ^ 1000 + 2 ^ 53 / 2 ^ 69 + 1 / 2 ^ 16 + 2 ^ 53 / 2 ^ 70 : ℝ) ≤
        1 / 100 := by norm_num
    have h11 : ((er * 2 ^ 53 * (101 / 100) + (Mr + er) * (101 / 100) + Mr + Mr * (101 / 100) +
        11 / 128) * T0 + (2 ^ 53 / 2 ^ 1000 + 2 ^ 53 / 2 ^ 69 + 1 / 2 ^ 16 +
          2 ^ 53 / 2 ^ 70)) * (s0 / 2 ^ 53) ≤ 7 / 10 * (s0 / 2 ^ 53) :=
      mul_le_mul_of_nonneg_right (by linarith) hsd53
    have h12 : 7 / 10 * (s0 / 2 ^ 53) = 7 / 10 / 2 ^ 53 * s0 := by ring
    linarith
  -- `w + w₂` rounds to a nearest word, and doubling keeps it nearest
  have hsumpos : s0 / 2 ≤ vw + vw2 := by
    have h3 := (abs_le.mp hS).1
    have h4 : (7 / 10 / 2 ^ 53 : ℝ) * s0 ≤ s0 / 2 := by
      have : (7 / 10 / 2 ^ 53 : ℝ) ≤ 1 / 2 := by norm_num
      nlinarith
    linarith
  have hsum1 : vw + vw2 < 2 := by
    have h3 := (abs_le.mp hS).2
    have h4 := Real.arcsin_le_pi_div_two s0
    have h5 := Real.pi_lt_d2
    have h6 : (7 / 10 / 2 ^ 53 : ℝ) * s0 ≤ 1 / 10 := by
      have : (7 / 10 / 2 ^ 53 : ℝ) ≤ 1 / 5 := by norm_num
      nlinarith
    linarith
  have hS0 : (1 : ℝ) / 2 ^ 28 ≤ vw + vw2 := by
    have : (1 : ℝ) / 2 ^ 28 = 1 / 2 ^ 27 / 2 := by norm_num
    linarith
  have hRd := add_rounded w.toBits w2.toBits hwf hw2.1 (ne_of_gt (by linarith)) (by
    rw [abs_of_pos (by linarith : (0 : ℝ) < vw + vw2)]
    linarith [(by norm_num : (2 : ℝ) < 2 ^ 1023)])
  rw [← F64Bits.toBits_add] at hRd
  set u := w + w2 with hud
  have hu := hRd.1
  have h994 : value (UInt64.ofNat (994 * 2 ^ 52)) = 1 / 2 ^ 29 := by
    rw [F64PositiveSpacing.boundary_value 994 (by norm_num) (by norm_num)]
    norm_num
  have huv : 1 / 2 ^ 29 ≤ |value u.toBits| := by
    have := F64RoundDouble.rounded_abs_ge u.toBits (vw + vw2) hRd 994 (by norm_num) (by
      rw [h994, abs_of_pos (by linarith : (0 : ℝ) < vw + vw2)]
      have : (1 : ℝ) / 2 ^ 29 ≤ 1 / 2 ^ 28 := by norm_num
      linarith)
    rwa [h994] at this
  have huv2 : |value u.toBits| < 2 ^ 900 := by
    have h3 := hRd.2.2.2 (UInt64.ofNat (1024 * 2 ^ 52))
    rw [AcosTheoremNeg.two_boundary, abs_two, abs_of_pos (by linarith : (0 : ℝ) < vw + vw2),
      abs_of_pos (by linarith : (0 : ℝ) < 2 - (vw + vw2))] at h3
    have h5 := le_abs_self (|value u.toBits| - (vw + vw2))
    linarith [(by norm_num : (4 : ℝ) < 2 ^ 900)]
  obtain ⟨h2f, h2v⟩ := AtanTheoremReduce.double_float u hu (le_trans (by norm_num) huv) huv2
  have hR2 := F64RoundDouble.rounded_double u.toBits (vw + vw2) hRd
    (by rw [abs_of_pos (by linarith : (0 : ℝ) < vw + vw2)]
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 28)])
    (by rw [abs_of_pos (by linarith : (0 : ℝ) < vw + vw2)]
        linarith [(by norm_num : (2 : ℝ) < 2 ^ 1000)])
    (2.0 * u).toBits h2f h2v
  -- the relative criterion
  have hy2 : Real.arccos v = 2 * Real.arcsin s0 := hy
  have harc0 : 0 ≤ Real.arcsin s0 := Real.arcsin_nonneg.mpr hs0n
  refine within_one_of_rounded_rel _ (2 * (vw + vw2)) (Real.arccos v) hR2 (7 / 10 / 2 ^ 53)
    (by norm_num) (by norm_num) ?_ ?_ ?_
  · rw [hy2, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.arcsin s0),
      show 2 * (vw + vw2) - 2 * Real.arcsin s0 = 2 * (vw + vw2 - Real.arcsin s0) by ring,
      abs_mul, abs_two]
    have h3 : 7 / 10 / 2 ^ 53 * s0 ≤ 7 / 10 / 2 ^ 53 * Real.arcsin s0 :=
      mul_le_mul_of_nonneg_left harc (by norm_num)
    linarith
  · rw [hy2, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.arcsin s0)]
    have : (1 : ℝ) / 2 ^ 1021 ≤ 2 * (1 / 2 ^ 27) := by norm_num
    linarith
  · rw [hy2, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * Real.arcsin s0)]
    have h3 := Real.arcsin_le_pi_div_two s0
    have h4 := Real.pi_lt_four
    linarith [(by norm_num : (4 : ℝ) < 2 ^ 1022)]

#print axioms pos_core

/-- `1/2 ≤ x < 1`, with the chain of `AsinTheoremRatio` for the range of `z`. -/
theorem pos_within (x : Float) (hx : Finite x.toBits) (h1 : 1 / 2 ≤ value x.toBits)
    (h2 : value x.toBits < 1) :
    F64SignedRounding.WithinSteps 1 (Real.arccos (value x.toBits))
      (posTail ((1.0 - x) * 0.5)).toBits := by
  obtain ⟨hzf, hzv, hz0⟩ := pos_z_exact x hx h1 h2
  set vz := (1 - value x.toBits) / 2 with hvz
  have hvzp : 0 < vz := lt_of_lt_of_le (by positivity) hz0
  have hvz4 : vz ≤ 1 / 4 := by rw [hvz]; linarith
  have ht : FSApprox ((1.0 - x) * 0.5) vz vz 1 (0 / 2 ^ 53) :=
    ((fsapprox_input _ hzf vz hvzp (by linarith) (by rw [hzv, abs_of_pos hvzp])).congr
      hzv).mono le_rfl (by norm_num)
  rcases le_or_gt vz (1 / 79) with ha | ha
  · have hr := ratio_A4 _ vz vz ht hvzp.le ha ha (le_trans (by norm_num) hz0)
    rw [ratio_eval] at hr
    exact pos_core x hx h1 h2 (1 / 79) _ _ (by norm_num) ha hr (by norm_num)
  rcases le_or_gt vz (1 / 20) with hb | hb
  · have hr := ratio_A3 _ vz vz ht (by linarith) hb hb (le_trans (by norm_num) hz0)
    rw [ratio_eval] at hr
    exact pos_core x hx h1 h2 (1 / 20) _ _ (by norm_num) hb hr (by norm_num)
  rcases le_or_gt vz (1 / 5) with hc | hc
  · have hr := ratio_A2 _ vz vz ht hb.le hc hc (le_trans (by norm_num) hz0)
    rw [ratio_eval] at hr
    exact pos_core x hx h1 h2 (1 / 5) _ _ (by norm_num) hc hr (by norm_num)
  · have hr := ratio_A1 _ vz vz ht hc.le hvz4 hvz4 (le_trans (by norm_num) hz0)
    rw [ratio_eval] at hr
    exact pos_core x hx h1 h2 (1 / 4) _ _ (by norm_num) hvz4 hr (by norm_num)

#print axioms pos_within

end Verified.Examples.AcosTheoremPos
