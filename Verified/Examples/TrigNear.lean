import Verified.Examples.TrigSinCos
import LeanExe.ProofKit.F64Approx

/-!
The errors of `Trig.sin` and `Trig.cos` as distances, for proofs that combine them with further
arithmetic.  `TrigSinCos` states one step from the nearest-even reference, which allows up to one
and a half spacings, about `3 · 2^-53` next to 1.  The kernels' own bounds are tighter: the sine
kernel rounds a real within `u (33/40 X³ + X/30)` of the sine of its argument, at most
`0.43 u` for `X ≤ 0.786`, and the cosine kernel's result lies within `7/5 u` of the cosine, with
`u = 2^-53`.  With the reduction's error of `|r|/2^59` and the quadrant selection of `TrigSinCos`,
every finite `x` gives `|sin x - Trig.sin x| ≤ (71/50) u` and the same for `cos` (`sin_near`,
`cos_near`).  The proofs follow `TrigSinCos.sin_within` and `cos_within` step by step and stop
before the conversion to steps.
-/

namespace Verified.Examples.TrigNear

open CodeLib.IEEE64 LeanExe.ProofKit TrigKernelWords TrigKernelSpec TrigCosKernel TrigReduce
  TrigStep F64SelfStep TrigQuadrant TrigSinCos F64Approx

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 1200

/-- The bound on the errors of `Trig.sin` and `Trig.cos`. -/
noncomputable def trigErr : ℝ := 71 / 50 * 𝐮

/-- The sine kernel's two bounds, combined into one distance. -/
theorem sin_kernel (c : UInt64) (t s X : ℝ) (hct : |value c - t| ≤ 𝐮 * |t|)
    (hts : |t - s| ≤ 𝐮 * (33 / 40 * X ^ 3 + X / 30)) (hX0 : 0 ≤ X) (hX1 : X ≤ 78541 / 100000)
    (hs : |s| ≤ 786 / 1000) : |value c - s| ≤ 122 / 100 * 𝐮 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : 0 ≤ 𝐮 := by rw [hu]; positivity
  have hX3 : X ^ 3 ≤ (78541 / 100000) ^ 3 := pow_le_pow_left₀ hX0 hX1 3
  have hk : 33 / 40 * X ^ 3 + X / 30 ≤ 43 / 100 := by norm_num at hX3 ⊢; linarith
  have hts' : |t - s| ≤ 43 / 100 * 𝐮 := by
    have := mul_le_mul_of_nonneg_left hk hu0
    linarith
  have ht : |t| ≤ 787 / 1000 := by
    have := abs_sub_abs_le_abs_sub t s
    have h43 : 43 / 100 * 𝐮 ≤ 1 / 1000 := by rw [hu]; norm_num
    linarith
  have hct' : |value c - t| ≤ 787 / 1000 * 𝐮 := by
    have := mul_le_mul_of_nonneg_left ht hu0
    linarith
  have := abs_sub_le (value c) t s
  linarith

/-- The kernels on a reduced argument, as distances from `sin r` and `cos r`. -/
theorem reduced_near (xa n : UInt64) (y0 y1 : Float) (hR : Reduced xa n y0.toBits y1.toBits) :
    ∃ N : Int, ((n.toNat % 4 : Nat) : Int) = N % 4 ∧
      FApprox (Trig.kernelSin y0 y1 true) (Real.sin (value xa - N * (Real.pi / 2))) trigErr ∧
      FApprox (Trig.kernelCos y0 y1) (Real.cos (value xa - N * (Real.pi / 2))) trigErr := by
  obtain ⟨N, hN, f0, f1, hacc, htail, hrl, hru⟩ := hR
  set r := value xa - N * (Real.pi / 2) with hr
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hr1 : |r| ≤ 78541 / 100000 := by
    have h17 : (1 : ℝ) / 2 ^ 17 ≤ 1 / 100000 := by norm_num
    linarith
  set X0 := |value y0.toBits| with hX0
  have hX0nn : 0 ≤ X0 := abs_nonneg _
  have hup : X0 ≤ |r| * (1 + 1 / 2 ^ 50) := by
    have h1 := abs_add_le (value y0.toBits + value y1.toBits) (-(value y1.toBits))
    rw [show value y0.toBits + value y1.toBits + -value y1.toBits = value y0.toBits by ring,
      abs_neg] at h1
    have h2 : |value y0.toBits + value y1.toBits| ≤ |r| + |r| / 2 ^ 60 := by
      have := abs_sub_abs_le_abs_sub (value y0.toBits + value y1.toBits) r
      linarith
    have h3 : X0 * (1 - 1 / 2 ^ 52) ≤ |r| * (1 + 1 / 2 ^ 60) := by
      rw [← hX0] at h1
      nlinarith
    nlinarith [abs_nonneg r]
  have hlo : 1 / 2 ^ 70 ≤ X0 := by
    have h1 := abs_add_le (value y0.toBits) (value y1.toBits)
    have h2 : |r| - |r| / 2 ^ 60 ≤ |value y0.toBits + value y1.toBits| := by
      have := abs_sub_abs_le_abs_sub r (value y0.toBits + value y1.toBits)
      have hc : |r - (value y0.toBits + value y1.toBits)| =
          |value y0.toBits + value y1.toBits - r| := abs_sub_comm _ _
      linarith
    have h3 : |r| * (1 - 1 / 2 ^ 60) ≤ X0 * (1 + 1 / 2 ^ 52) := by
      rw [← hX0] at h1
      nlinarith
    nlinarith [abs_nonneg r]
  have hX1 : X0 ≤ 78541 / 100000 := by
    have h17 : (1 : ℝ) / 2 ^ 17 ≤ 1 / 100000 := by norm_num
    nlinarith [abs_nonneg r]
  have hy : |value y1.toBits| ≤ X0 / 2 ^ 52 := htail
  have har : |value y0.toBits + value y1.toBits - r| ≤ |r| / 2 ^ 59 :=
    hacc.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num))
  have hr59 : |r| / 2 ^ 59 ≤ 1 / 2 ^ 59 := div_le_div_of_nonneg_right (hr1.trans (by norm_num))
    (by positivity)
  refine ⟨N, by push_cast; exact hN, ?_, ?_⟩
  · obtain ⟨hcf, t, hct, hts⟩ := sinTail_spec y0.toBits y1.toBits X0 f0 f1 rfl hlo hX1 hy
    refine ⟨by rw [kernelSin_tail_bits]; exact hcf, ?_⟩
    rw [kernelSin_tail_bits]
    have hs := (Real.abs_sin_sub_sin_le (value y0.toBits + value y1.toBits) r).trans har
    have hsy : |Real.sin (value y0.toBits + value y1.toBits)| ≤ 786 / 1000 := by
      refine (Real.abs_sin_le_abs).trans ?_
      have := abs_sub_abs_le_abs_sub (value y0.toBits + value y1.toBits) r
      have h59 : |r| / 2 ^ 59 ≤ 1 / 2 ^ 59 := hr59
      norm_num at h59
      linarith
    have hk := sin_kernel _ t _ X0 hct hts hX0nn hX1 hsy
    have := abs_sub_le (value (sinTailW y0.toBits y1.toBits))
      (Real.sin (value y0.toBits + value y1.toBits)) (Real.sin r)
    unfold trigErr
    rw [hu] at hk ⊢
    linarith
  · obtain ⟨hcf, hc⟩ := cos_spec y0.toBits y1.toBits X0 f0 f1 rfl hlo hX1 hy
    refine ⟨by rw [kernelCos_bits]; exact hcf, ?_⟩
    rw [kernelCos_bits]
    have hs := (Real.abs_cos_sub_cos_le (value y0.toBits + value y1.toBits) r).trans har
    unfold trigErr
    calc |value (cosW y0.toBits y1.toBits) - Real.cos r|
        ≤ |value (cosW y0.toBits y1.toBits) - Real.cos (value y0.toBits + value y1.toBits)| +
          |Real.cos (value y0.toBits + value y1.toBits) - Real.cos r| := abs_sub_le _ _ _
      _ ≤ 7 / 5 * 𝐮 + 1 / 2 ^ 59 := by linarith
      _ ≤ 71 / 50 * 𝐮 := by rw [hu]; norm_num

theorem neg_near {f : Float} {v e : ℝ} (h : FApprox f v e) : FApprox (-f) (-v) e :=
  fapprox_neg h

/-- The quadrant selection of `sinWith`, as distances. -/
theorem sin_select_near (n : UInt64) (y0 y1 : Float) (v : ℝ) (N : Int)
    (hk : ((n.toNat % 4 : Nat) : Int) = N % 4)
    (hsin : FApprox (Trig.kernelSin y0 y1 true) (Real.sin (v - N * (Real.pi / 2))) trigErr)
    (hcos : FApprox (Trig.kernelCos y0 y1) (Real.cos (v - N * (Real.pi / 2))) trigErr) :
    FApprox (if n &&& 3 == 0 then Trig.kernelSin y0 y1 true
        else if n &&& 3 == 1 then Trig.kernelCos y0 y1
        else if n &&& 3 == 2 then -Trig.kernelSin y0 y1 true
        else -Trig.kernelCos y0 y1) (Real.sin v) trigErr := by
  have hq := quadrant (v - N * (Real.pi / 2)) N (n.toNat % 4) hk
  rw [show v - N * (Real.pi / 2) + N * (Real.pi / 2) = v by ring] at hq
  obtain ⟨q0, q1, q2, q3⟩ := hq
  have hlt : n.toNat % 4 < 4 := Nat.mod_lt _ (by norm_num)
  simp only [q_beq]
  obtain ⟨k, hkdef⟩ : ∃ k, n.toNat % 4 = k := ⟨_, rfl⟩
  rw [hkdef] at q0 q1 q2 q3 hlt ⊢
  interval_cases k
  · simp only [UInt64.reduceToNat, decide_true, ite_true]
    rw [(q0 rfl).1]; exact hsin
  · simp only [UInt64.reduceToNat, decide_true, ite_true, show ¬ (1 = 0) by omega, decide_false,
      Bool.false_eq_true, ite_false]
    rw [(q1 rfl).1]; exact hcos
  · simp only [UInt64.reduceToNat, decide_true, ite_true, show ¬ (2 = 0) by omega,
      show ¬ (2 = 1) by omega, decide_false, Bool.false_eq_true, ite_false]
    rw [(q2 rfl).1]; exact neg_near hsin
  · simp only [UInt64.reduceToNat, show ¬ (3 = 0) by omega, show ¬ (3 = 1) by omega,
      show ¬ (3 = 2) by omega, decide_false, Bool.false_eq_true, ite_false]
    rw [(q3 rfl).1]; exact neg_near hcos

/-- The quadrant selection of `cosWith`, as distances. -/
theorem cos_select_near (n : UInt64) (y0 y1 : Float) (v : ℝ) (N : Int)
    (hk : ((n.toNat % 4 : Nat) : Int) = N % 4)
    (hsin : FApprox (Trig.kernelSin y0 y1 true) (Real.sin (v - N * (Real.pi / 2))) trigErr)
    (hcos : FApprox (Trig.kernelCos y0 y1) (Real.cos (v - N * (Real.pi / 2))) trigErr) :
    FApprox (if n &&& 3 == 0 then Trig.kernelCos y0 y1
        else if n &&& 3 == 1 then -Trig.kernelSin y0 y1 true
        else if n &&& 3 == 2 then -Trig.kernelCos y0 y1
        else Trig.kernelSin y0 y1 true) (Real.cos v) trigErr := by
  have hq := quadrant (v - N * (Real.pi / 2)) N (n.toNat % 4) hk
  rw [show v - N * (Real.pi / 2) + N * (Real.pi / 2) = v by ring] at hq
  obtain ⟨q0, q1, q2, q3⟩ := hq
  have hlt : n.toNat % 4 < 4 := Nat.mod_lt _ (by norm_num)
  simp only [q_beq]
  obtain ⟨k, hkdef⟩ : ∃ k, n.toNat % 4 = k := ⟨_, rfl⟩
  rw [hkdef] at q0 q1 q2 q3 hlt ⊢
  interval_cases k
  · simp only [UInt64.reduceToNat, decide_true, ite_true]
    rw [(q0 rfl).2]; exact hcos
  · simp only [UInt64.reduceToNat, decide_true, ite_true, show ¬ (1 = 0) by omega, decide_false,
      Bool.false_eq_true, ite_false]
    rw [(q1 rfl).2]; exact neg_near hsin
  · simp only [UInt64.reduceToNat, decide_true, ite_true, show ¬ (2 = 0) by omega,
      show ¬ (2 = 1) by omega, decide_false, Bool.false_eq_true, ite_false]
    rw [(q2 rfl).2]; exact neg_near hcos
  · simp only [UInt64.reduceToNat, show ¬ (3 = 0) by omega, show ¬ (3 = 1) by omega,
      show ¬ (3 = 2) by omega, decide_false, Bool.false_eq_true, ite_false]
    rw [(q3 rfl).2]; exact hsin

/-- `|x - sin x| ≤ trigErr` for `|x| < 2 ^ -26`, where `sin` returns `x`. -/
theorem tiny_sin_near (x : UInt64) (hx : |value x| < 1 / 2 ^ 26) :
    |value x - Real.sin (value x)| ≤ trigErr := by
  have hb := Real.sin_bound (x := value x) (hx.le.trans (by norm_num))
  set A := |value x| with hAdef
  have hA0 : 0 ≤ A := abs_nonneg _
  have hA3 : A ^ 3 ≤ (1 / 2 ^ 26) ^ 3 := pow_le_pow_left₀ hA0 hx.le 3
  have hA5 : A ^ 5 ≤ (1 / 2 ^ 26) ^ 5 := pow_le_pow_left₀ hA0 hx.le 5
  have hv3 : |value x ^ 3| = A ^ 3 := by rw [abs_pow]
  have hv3' := abs_le.mp (le_of_eq hv3)
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  unfold trigErr
  rw [hu]
  norm_num at hA3 hA5
  rw [abs_le] at hb ⊢
  constructor <;> linarith [hv3'.1, hv3'.2, hb.1, hb.2]

/-- The error of `Trig.sin` for every finite `x`. -/
theorem sin_near (x : Float) (hxf : Finite x.toBits) :
    FApprox (Trig.sin x) (Real.sin (value x.toBits)) trigErr := by
  have hix := TrigSinCos.high_word x.toBits
  have hfin := finite_bound x.toBits hxf
  have habs := abs_toNat x.toBits
  have hav := abs_value x.toBits
  have haf := abs_finite x.toBits hxf
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  obtain ⟨t26, t21, -⟩ := threshold_values
  have hA63 : (Wasm.IEEE64.abs x.toBits).toNat < 2 ^ 63 := by rw [habs]; omega
  unfold Trig.sin Trig.sinWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
  by_cases h1 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 ≤ 1072243195
  · rw [if_pos h1]
    by_cases h2 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 1045430272
    · rw [if_pos h2]
      refine ⟨hxf, tiny_sin_near x.toBits ?_⟩
      rw [← hav, ← t26]
      exact F64PositiveOrder.value_strict (by decide) (by
        rw [habs]
        show _ < 0x3E50000000000000
        omega)
    · rw [if_neg h2]
      have hlo : 1 / 2 ^ 26 ≤ |value x.toBits| := by
        rw [← hav, ← t26]
        exact (F64PositiveOrder.value_le_iff (by decide) hA63).mpr (by
          rw [habs]
          show 0x3E50000000000000 ≤ _
          omega)
      have hhi : |value x.toBits| < 1647100 / 2 ^ 21 := by
        rw [← hav, ← t21]
        exact F64PositiveOrder.value_strict (by decide) (by
          rw [habs]
          show _ < 0x3FE921FC00000000
          omega)
      unfold FApprox Approx
      rw [kernelSin_direct_bits]
      obtain ⟨hcf, t, hct, hts⟩ := sinDirect_spec x.toBits |value x.toBits| hxf rfl
        (le_trans (by norm_num) hlo) (le_trans hhi.le (by norm_num))
      have hs : |Real.sin (value x.toBits)| ≤ 786 / 1000 :=
        Real.abs_sin_le_abs.trans (hhi.le.trans (by norm_num))
      have hk := sin_kernel _ t _ _ hct hts (abs_nonneg _) (le_trans hhi.le (by norm_num)) hs
      refine ⟨hcf, hk.trans ?_⟩
      unfold trigErr
      rw [hu]
      norm_num
  · rw [if_neg h1]
    have h3 : ¬ (2146435072 ≤ x.toBits.toNat % 2 ^ 63 / 2 ^ 32) := by omega
    rw [if_neg h3]
    have hR := TrigReduce.remPio2_spec x.abs (by rw [F64Bits.toBits_abs]; exact hA63)
      (by rw [F64Bits.toBits_abs, habs]; omega) (by rw [F64Bits.toBits_abs, habs]; omega)
    generalize Trig.remPio2 Trig.invPi Trig.halfPi x.abs = P at hR ⊢
    obtain ⟨n, y0, y1⟩ := P
    dsimp only at hR ⊢
    rw [F64Bits.toBits_abs] at hR
    obtain ⟨N, hk, hsin, hcos⟩ := reduced_near _ n y0 y1 hR
    have hsel := sin_select_near n y0 y1 _ N hk hsin hcos
    rw [hav] at hsel
    by_cases hneg : x < 0.0
    · have hv := (lt_zero_iff x hxf).mp hneg
      rw [if_pos hneg]
      rw [abs_of_neg hv, Real.sin_neg] at hsel
      have := neg_near hsel
      rwa [neg_neg] at this
    · have hv : 0 ≤ value x.toBits := not_lt.mp (fun h => hneg ((lt_zero_iff x hxf).mpr h))
      rw [if_neg hneg]
      rwa [abs_of_nonneg hv] at hsel

/-- The error of `Trig.cos` for every finite `x`. -/
theorem cos_near (x : Float) (hxf : Finite x.toBits) :
    FApprox (Trig.cos x) (Real.cos (value x.toBits)) trigErr := by
  have hix := TrigSinCos.high_word x.toBits
  have hfin := finite_bound x.toBits hxf
  have habs := abs_toNat x.toBits
  have hav := abs_value x.toBits
  have haf := abs_finite x.toBits hxf
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  obtain ⟨-, t21, t47⟩ := threshold_values
  have hA63 : (Wasm.IEEE64.abs x.toBits).toNat < 2 ^ 63 := by rw [habs]; omega
  unfold Trig.cos Trig.cosWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
  by_cases h1 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 ≤ 1072243195
  · rw [if_pos h1]
    by_cases h2 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 1044816030
    · rw [if_pos h2]
      have hhi : |value x.toBits| < 1482910 / 2 ^ 47 := by
        rw [← hav, ← t47]
        exact F64PositiveOrder.value_strict (by decide) (by
          rw [habs]
          show _ < 0x3E46A09E00000000
          omega)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h1b⟩ := const_bits
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, fo⟩ := words_finite
      unfold FApprox Approx
      rw [h1b, value_one]
      refine ⟨fo, ?_⟩
      have hc := Real.one_sub_sq_div_two_le_cos (x := value x.toBits)
      have hc1 := Real.cos_le_one (value x.toBits)
      have hx2 : value x.toBits ^ 2 ≤ (1482910 / 2 ^ 47) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hhi.le 2
      have hx2' : value x.toBits ^ 2 ≤ 1 / 2 ^ 52 := hx2.trans (by norm_num)
      unfold trigErr
      rw [hu, abs_le]
      constructor <;> linarith
    · rw [if_neg h2]
      have hlo : 1482910 / 2 ^ 47 ≤ |value x.toBits| := by
        rw [← hav, ← t47]
        exact (F64PositiveOrder.value_le_iff (by decide) hA63).mpr (by
          rw [habs]
          show 0x3E46A09E00000000 ≤ _
          omega)
      have hhi : |value x.toBits| < 1647100 / 2 ^ 21 := by
        rw [← hav, ← t21]
        exact F64PositiveOrder.value_strict (by decide) (by
          rw [habs]
          show _ < 0x3FE921FC00000000
          omega)
      have h0 : (0.0 : Float).toBits = 0 := by decide
      have h0f : Finite (0 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
      have h0v : value (0 : UInt64) = 0 := (zero_iff 0).mp (by decide)
      unfold FApprox Approx
      rw [kernelCos_bits, h0]
      obtain ⟨hcf, hc⟩ := cos_spec x.toBits 0 |value x.toBits| hxf h0f rfl
        (le_trans (by norm_num) hlo) (le_trans hhi.le (by norm_num))
        (by rw [h0v, abs_zero]; positivity)
      rw [h0v, add_zero] at hc
      refine ⟨hcf, hc.trans ?_⟩
      unfold trigErr
      rw [hu]
      norm_num
  · rw [if_neg h1]
    have h3 : ¬ (2146435072 ≤ x.toBits.toNat % 2 ^ 63 / 2 ^ 32) := by omega
    rw [if_neg h3]
    have hR := TrigReduce.remPio2_spec x.abs (by rw [F64Bits.toBits_abs]; exact hA63)
      (by rw [F64Bits.toBits_abs, habs]; omega) (by rw [F64Bits.toBits_abs, habs]; omega)
    generalize Trig.remPio2 Trig.invPi Trig.halfPi x.abs = P at hR ⊢
    obtain ⟨n, y0, y1⟩ := P
    dsimp only at hR ⊢
    rw [F64Bits.toBits_abs] at hR
    obtain ⟨N, hk, hsin, hcos⟩ := reduced_near _ n y0 y1 hR
    have hsel := cos_select_near n y0 y1 _ N hk hsin hcos
    rwa [hav, Real.cos_abs] at hsel

#print axioms sin_kernel
#print axioms reduced_near
#print axioms sin_select_near
#print axioms cos_select_near
#print axioms tiny_sin_near
#print axioms sin_near
#print axioms cos_near

end Verified.Examples.TrigNear
