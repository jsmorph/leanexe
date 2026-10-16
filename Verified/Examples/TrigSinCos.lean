import Verified.Examples.TrigQuadrant
import LeanExe.ProofKit.F64SelfStep

/-!
The accuracy of `Trig.sin` and `Trig.cos`: for every finite `x`, the result lies within one
step of the nearest-even reference of `sin x` and `cos x`.
-/

namespace Verified.Examples.TrigSinCos

open CodeLib.IEEE64 LeanExe.ProofKit TrigKernelWords TrigKernelSpec TrigCosKernel TrigReduce
  TrigStep F64SelfStep TrigQuadrant

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 1200

theorem abs_toNat (w : UInt64) : (Wasm.IEEE64.abs w).toNat = w.toNat % 2 ^ 63 := by
  unfold Wasm.IEEE64.abs Wasm.IEEE64.encodeFinite Wasm.IEEE64.exponent Wasm.IEEE64.fraction
  simp only [Bool.false_eq_true, ite_false, zero_add]
  have h1 : w.toNat / 2 ^ 52 % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have h2 : w.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
  omega

theorem abs_value (w : UInt64) : value (Wasm.IEEE64.abs w) = |value w| := by
  obtain ⟨he, hf, hs⟩ := F64Sign.fields_abs w
  have hm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.abs w) = Wasm.IEEE64.scaledMagnitude w := by
    simp [Wasm.IEEE64.scaledMagnitude, he, hf]
  rw [TrigSmall.value_of_scaled, TrigSmall.value_of_scaled, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
  congr 1
  unfold Wasm.IEEE64.scaledValue
  rw [hs, hm]
  simp only [Bool.false_eq_true, ite_false]
  cases Wasm.IEEE64.sign w <;> simp

theorem abs_finite (w : UInt64) (h : Finite w) : Finite (Wasm.IEEE64.abs w) := by
  obtain ⟨he, -, -⟩ := F64Sign.fields_abs w
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at h ⊢
  rw [he]
  exact h

/-- Negating a result within one step of `v` gives a result within one step of `-v`. -/
theorem neg_within (f : Float) (v : ℝ) (h : F64SignedRounding.WithinSteps 1 v f.toBits) :
    F64SignedRounding.WithinSteps 1 (-v) (-f).toBits := by
  have hn : Wasm.IEEE64.isNaN f.toBits = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    have h1 := h.1
    simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at hc
    omega
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, hn]
  exact (F64SignedRounding.within_negate 1 v f.toBits).mpr h

theorem land_three (n : UInt64) : (n &&& 3).toNat = n.toNat % 4 := by
  rw [UInt64.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod n.toNat 2

theorem lt_zero_iff (x : Float) (hxf : Finite x.toBits) : x < 0.0 ↔ value x.toBits < 0 := by
  have h0 : (0.0 : Float).toBits = 0 := by decide
  have hn : Wasm.IEEE64.isNaN x.toBits = false := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at hxf
    unfold Wasm.IEEE64.isNaN
    simp only [bne_iff_ne, ne_eq] at hxf
    simp [hxf]
  rw [F64Bits.lt_iff, h0]
  unfold Wasm.IEEE64.lt
  rw [hn, TrigSmall.value_of_scaled]
  have hz : Wasm.IEEE64.isNaN (0 : UInt64) = false := by decide
  have hs : Wasm.IEEE64.scaledValue (0 : UInt64) = 0 := by decide
  simp only [hz, hs, Bool.false_or, Bool.false_eq_true, ite_false, decide_eq_true_eq]
  constructor
  · intro h
    exact div_neg_of_neg_of_pos (by exact_mod_cast h) (by positivity)
  · intro h
    by_contra hc
    have : (0 : ℝ) ≤ (Wasm.IEEE64.scaledValue x.toBits : ℝ) := by exact_mod_cast not_lt.mp hc
    have := div_nonneg this (show (0 : ℝ) ≤ 2 ^ 1074 by positivity)
    linarith

/-- The high word of `|x|` and its comparisons. -/
theorem high_word (w : UInt64) :
    ((w >>> 32) &&& 0x7fffffff).toNat = w.toNat % 2 ^ 63 / 2 ^ 32 := by
  rw [UInt64.toNat_and, TrigWords.shr_toNat]
  have h1 : (0x7fffffff : UInt64).toNat = 2 ^ 31 - 1 := rfl
  have h2 : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `sin x` for `|x| < 2 ^ -26`, where `sin` returns `x`. -/
theorem tiny_sin (x : UInt64) (hxf : Finite x) (hx : |value x| < 1 / 2 ^ 26)
    (hA : x.toNat % 2 ^ 63 = 0 ↔ value x = 0) :
    F64SignedRounding.WithinSteps 1 (Real.sin (value x)) x := by
  by_cases h0 : value x = 0
  · rw [h0, Real.sin_zero]
    exact zero_step x (hA.mpr h0)
  · refine self_step x _ hxf h0 (hx.le.trans (by norm_num)) ?_
    have hb := Real.sin_bound (x := value x) (hx.le.trans (by norm_num))
    set A := |value x| with hAdef
    have hA0 : 0 ≤ A := abs_nonneg _
    have hA2 : A ^ 2 ≤ 1 / 2 ^ 52 := by
      have := pow_le_pow_left₀ hA0 hx.le 2
      rw [div_pow, one_pow, ← pow_mul] at this
      exact this
    have hA3 : A ^ 3 ≤ A / 2 ^ 52 := by
      rw [show A ^ 3 = A * A ^ 2 by ring, show A / 2 ^ 52 = A * (1 / 2 ^ 52) by ring]
      exact mul_le_mul_of_nonneg_left hA2 hA0
    have hA5 : A ^ 5 ≤ A / 2 ^ 104 := by
      have h4 : (A ^ 2) ^ 2 ≤ (1 / 2 ^ 52) ^ 2 := pow_le_pow_left₀ (by positivity) hA2 2
      rw [show A ^ 5 = A * (A ^ 2) ^ 2 by ring, show A / 2 ^ 104 = A * (1 / 2 ^ 52) ^ 2 by
        rw [div_pow, one_pow, ← pow_mul]; ring]
      exact mul_le_mul_of_nonneg_left h4 hA0
    have hv3 : |value x ^ 3| = A ^ 3 := by rw [abs_pow]
    have hv3' := abs_le.mp (le_of_eq hv3)
    rw [abs_le] at hb ⊢
    constructor <;> nlinarith [hv3'.1, hv3'.2]

theorem q_beq (n c : UInt64) : (n &&& 3 == c) = decide (n.toNat % 4 = c.toNat) := by
  rw [← land_three]
  by_cases h : n &&& 3 = c
  · rw [beq_iff_eq.mpr h, h]
    exact (decide_eq_true rfl).symm
  · have h' : (n &&& 3).toNat ≠ c.toNat := fun h' => h (UInt64.toNat_inj.mp h')
    rw [beq_eq_false_iff_ne.mpr h, decide_eq_false h']

/-- The quadrant selection of `sinWith` on a reduced argument. -/
theorem sin_select (n : UInt64) (y0 y1 : Float) (v : ℝ) (N : Int)
    (hk : ((n.toNat % 4 : Nat) : Int) = N % 4)
    (hsin : F64SignedRounding.WithinSteps 1 (Real.sin (v - N * (Real.pi / 2)))
      (Trig.kernelSin y0 y1 true).toBits)
    (hcos : F64SignedRounding.WithinSteps 1 (Real.cos (v - N * (Real.pi / 2)))
      (Trig.kernelCos y0 y1).toBits) :
    F64SignedRounding.WithinSteps 1 (Real.sin v)
      (if n &&& 3 == 0 then Trig.kernelSin y0 y1 true
        else if n &&& 3 == 1 then Trig.kernelCos y0 y1
        else if n &&& 3 == 2 then -Trig.kernelSin y0 y1 true
        else -Trig.kernelCos y0 y1).toBits := by
  have hq := quadrant (v - N * (Real.pi / 2)) N (n.toNat % 4) hk
  rw [show v - N * (Real.pi / 2) + N * (Real.pi / 2) = v by ring] at hq
  obtain ⟨q0, q1, q2, q3⟩ := hq
  have hlt : n.toNat % 4 < 4 := Nat.mod_lt _ (by norm_num)
  simp only [q_beq]
  obtain ⟨k, hkdef⟩ : ∃ k, n.toNat % 4 = k := ⟨_, rfl⟩
  rw [hkdef] at q0 q1 q2 q3 hlt ⊢
  interval_cases k
  · simp only [UInt64.reduceToNat, decide_true, ite_true]
    rw [(q0 rfl).1]
    exact hsin
  · simp only [UInt64.reduceToNat, decide_true, ite_true, show ¬ (1 = 0) by omega, decide_false,
      Bool.false_eq_true, ite_false]
    rw [(q1 rfl).1]
    exact hcos
  · simp only [UInt64.reduceToNat, decide_true, ite_true, show ¬ (2 = 0) by omega,
      show ¬ (2 = 1) by omega, decide_false, Bool.false_eq_true, ite_false]
    rw [(q2 rfl).1]
    exact neg_within _ _ hsin
  · simp only [UInt64.reduceToNat, show ¬ (3 = 0) by omega, show ¬ (3 = 1) by omega,
      show ¬ (3 = 2) by omega, decide_false, Bool.false_eq_true, ite_false]
    rw [(q3 rfl).1]
    exact neg_within _ _ hcos

/-- The quadrant selection of `cosWith` on a reduced argument. -/
theorem cos_select (n : UInt64) (y0 y1 : Float) (v : ℝ) (N : Int)
    (hk : ((n.toNat % 4 : Nat) : Int) = N % 4)
    (hsin : F64SignedRounding.WithinSteps 1 (Real.sin (v - N * (Real.pi / 2)))
      (Trig.kernelSin y0 y1 true).toBits)
    (hcos : F64SignedRounding.WithinSteps 1 (Real.cos (v - N * (Real.pi / 2)))
      (Trig.kernelCos y0 y1).toBits) :
    F64SignedRounding.WithinSteps 1 (Real.cos v)
      (if n &&& 3 == 0 then Trig.kernelCos y0 y1
        else if n &&& 3 == 1 then -Trig.kernelSin y0 y1 true
        else if n &&& 3 == 2 then -Trig.kernelCos y0 y1
        else Trig.kernelSin y0 y1 true).toBits := by
  have hq := quadrant (v - N * (Real.pi / 2)) N (n.toNat % 4) hk
  rw [show v - N * (Real.pi / 2) + N * (Real.pi / 2) = v by ring] at hq
  obtain ⟨q0, q1, q2, q3⟩ := hq
  have hlt : n.toNat % 4 < 4 := Nat.mod_lt _ (by norm_num)
  simp only [q_beq]
  obtain ⟨k, hkdef⟩ : ∃ k, n.toNat % 4 = k := ⟨_, rfl⟩
  rw [hkdef] at q0 q1 q2 q3 hlt ⊢
  interval_cases k
  · simp only [UInt64.reduceToNat, decide_true, ite_true]
    rw [(q0 rfl).2]
    exact hcos
  · simp only [UInt64.reduceToNat, decide_true, ite_true, show ¬ (1 = 0) by omega, decide_false,
      Bool.false_eq_true, ite_false]
    rw [(q1 rfl).2]
    exact neg_within _ _ hsin
  · simp only [UInt64.reduceToNat, decide_true, ite_true, show ¬ (2 = 0) by omega,
      show ¬ (2 = 1) by omega, decide_false, Bool.false_eq_true, ite_false]
    rw [(q2 rfl).2]
    exact neg_within _ _ hcos
  · simp only [UInt64.reduceToNat, show ¬ (3 = 0) by omega, show ¬ (3 = 1) by omega,
      show ¬ (3 = 2) by omega, decide_false, Bool.false_eq_true, ite_false]
    rw [(q3 rfl).2]
    exact hsin

theorem finite_bound (w : UInt64) (h : Finite w) : w.toNat % 2 ^ 63 < 0x7FF0000000000000 := by
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent at h
  simp only [bne_iff_ne, ne_eq] at h
  omega

theorem zero_iff (w : UInt64) : w.toNat % 2 ^ 63 = 0 ↔ value w = 0 := by
  have hav := abs_value w
  have habs := abs_toNat w
  have h0 : value (0 : UInt64) = 0 := by
    rw [TrigSmall.value_of_scaled]
    have : Wasm.IEEE64.scaledValue (0 : UInt64) = 0 := by decide
    rw [this]
    simp
  constructor
  · intro h
    have : Wasm.IEEE64.abs w = 0 := UInt64.toNat_inj.mp (by rw [habs, h]; rfl)
    rw [this, h0] at hav
    exact abs_eq_zero.mp hav.symm
  · intro h
    by_contra hc
    have hlt := F64PositiveOrder.value_strict (left := 0) (right := Wasm.IEEE64.abs w)
      (by rw [habs]; omega) (by rw [habs]; show 0 < _; omega)
    rw [h0, hav, h, abs_zero] at hlt
    exact lt_irrefl _ hlt

/-- Values of the high-word thresholds. -/
theorem threshold_values :
    value (0x3E50000000000000 : UInt64) = 1 / 2 ^ 26 ∧
      value (0x3FE921FC00000000 : UInt64) = 1647100 / 2 ^ 21 ∧
      value (0x3E46A09E00000000 : UInt64) = 1482910 / 2 ^ 47 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [TrigReduce.value_word _ 1 26 (by norm_num) (by decide +kernel)]
    norm_num
  · rw [TrigReduce.value_word _ 1647100 21 (by norm_num) (by decide +kernel)]
    norm_num
  · rw [TrigReduce.value_word _ 1482910 47 (by norm_num) (by decide +kernel)]
    norm_num

/-- The accuracy of `Trig.sin` for every finite `x`. -/
theorem sin_within (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.sin (value x.toBits)) (Trig.sin x).toBits := by
  have hix := high_word x.toBits
  have hfin := finite_bound x.toBits hxf
  have habs := abs_toNat x.toBits
  have hav := abs_value x.toBits
  have haf := abs_finite x.toBits hxf
  obtain ⟨t26, t21, -⟩ := threshold_values
  have hA63 : (Wasm.IEEE64.abs x.toBits).toNat < 2 ^ 63 := by rw [habs]; omega
  unfold Trig.sin Trig.sinWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
  by_cases h1 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 ≤ 1072243195
  · rw [if_pos h1]
    by_cases h2 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 1045430272
    · -- `|x| < 2 ^ -26`: the result is `x`.
      rw [if_pos h2]
      refine tiny_sin x.toBits hxf ?_ (zero_iff x.toBits)
      rw [← hav, ← t26]
      exact F64PositiveOrder.value_strict (by decide) (by
        rw [habs]
        show _ < 0x3E50000000000000
        omega)
    · -- `2 ^ -26 ≤ |x| < 0x3FE921FC00000000`: the kernel without a tail.
      rw [if_neg h2]
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
      rw [kernelSin_direct_bits]
      obtain ⟨hcf, t, hct, hts⟩ := sinDirect_spec x.toBits |value x.toBits| hxf rfl
        (le_trans (by norm_num) hlo) (le_trans hhi.le (by norm_num))
      exact sin_final _ t _ _ _ hcf hct hts (by rw [sub_self, abs_zero]; positivity)
        (abs_nonneg _) (le_mul_of_one_le_right (abs_nonneg _) (by norm_num))
        (le_trans (by norm_num) hlo) (le_trans hhi.le (by norm_num))
  · rw [if_neg h1]
    have h3 : ¬ (2146435072 ≤ x.toBits.toNat % 2 ^ 63 / 2 ^ 32) := by omega
    rw [if_neg h3]
    -- The reduced argument.
    have hR := TrigReduce.remPio2_spec x.abs (by rw [F64Bits.toBits_abs]; exact hA63)
      (by rw [F64Bits.toBits_abs, habs]; omega) (by rw [F64Bits.toBits_abs, habs]; omega)
    generalize Trig.remPio2 Trig.invPi Trig.halfPi x.abs = P at hR ⊢
    obtain ⟨n, y0, y1⟩ := P
    dsimp only at hR ⊢
    rw [F64Bits.toBits_abs] at hR
    obtain ⟨N, hk, hsin, hcos⟩ := reduced_kernels _ n y0 y1 hR
    have hsel := sin_select n y0 y1 _ N hk hsin hcos
    rw [hav] at hsel
    by_cases hneg : x < 0.0
    · have hv := (lt_zero_iff x hxf).mp hneg
      rw [if_pos hneg]
      rw [abs_of_neg hv, Real.sin_neg] at hsel
      have := neg_within _ _ hsel
      rwa [neg_neg] at this
    · have hv : 0 ≤ value x.toBits := not_lt.mp (fun h => hneg ((lt_zero_iff x hxf).mpr h))
      rw [if_neg hneg]
      rwa [abs_of_nonneg hv] at hsel

/-- The accuracy of `Trig.cos` for every finite `x`. -/
theorem cos_within (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.cos (value x.toBits)) (Trig.cos x).toBits := by
  have hix := high_word x.toBits
  have hfin := finite_bound x.toBits hxf
  have habs := abs_toNat x.toBits
  have hav := abs_value x.toBits
  have haf := abs_finite x.toBits hxf
  obtain ⟨-, t21, t47⟩ := threshold_values
  have hA63 : (Wasm.IEEE64.abs x.toBits).toNat < 2 ^ 63 := by rw [habs]; omega
  unfold Trig.cos Trig.cosWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
  by_cases h1 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 ≤ 1072243195
  · rw [if_pos h1]
    by_cases h2 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 1044816030
    · -- `|x| < 0x3E46A09E00000000`: the result is 1.
      rw [if_pos h2]
      have hhi : |value x.toBits| < 1482910 / 2 ^ 47 := by
        rw [← hav, ← t47]
        exact F64PositiveOrder.value_strict (by decide) (by
          rw [habs]
          show _ < 0x3E46A09E00000000
          omega)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h1b⟩ := const_bits
      rw [h1b]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, fo⟩ := words_finite
      have hc := Real.one_sub_sq_div_two_le_cos (x := value x.toBits)
      have hc1 := Real.cos_le_one (value x.toBits)
      have hx2 : value x.toBits ^ 2 ≤ (1482910 / 2 ^ 47) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hhi.le 2
      have hx2' : value x.toBits ^ 2 ≤ 1 / 2 ^ 52 := hx2.trans (by norm_num)
      refine F64UnitStep.unit_step _ one fo ?_ (Real.abs_cos_le_one _) ?_
      · rw [abs_of_nonneg (by linarith)]
        linarith
      · rw [value_one, abs_lt]
        constructor <;> linarith
    · -- The kernel without a tail.
      rw [if_neg h2]
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
      rw [kernelCos_bits, h0]
      obtain ⟨hcf, hc⟩ := cos_spec x.toBits 0 |value x.toBits| hxf h0f rfl
        (le_trans (by norm_num) hlo) (le_trans hhi.le (by norm_num))
        (by rw [h0v, abs_zero]; positivity)
      rw [h0v, add_zero] at hc
      exact cos_final _ _ _ hcf hc (by rw [sub_self, abs_zero]; positivity)
        (le_trans hhi.le (by norm_num))
  · rw [if_neg h1]
    have h3 : ¬ (2146435072 ≤ x.toBits.toNat % 2 ^ 63 / 2 ^ 32) := by omega
    rw [if_neg h3]
    have hR := TrigReduce.remPio2_spec x.abs (by rw [F64Bits.toBits_abs]; exact hA63)
      (by rw [F64Bits.toBits_abs, habs]; omega) (by rw [F64Bits.toBits_abs, habs]; omega)
    generalize Trig.remPio2 Trig.invPi Trig.halfPi x.abs = P at hR ⊢
    obtain ⟨n, y0, y1⟩ := P
    dsimp only at hR ⊢
    rw [F64Bits.toBits_abs] at hR
    obtain ⟨N, hk, hsin, hcos⟩ := reduced_kernels _ n y0 y1 hR
    have hsel := cos_select n y0 y1 _ N hk hsin hcos
    rwa [hav, Real.cos_abs] at hsel

#print axioms abs_toNat
#print axioms abs_value
#print axioms neg_within
#print axioms lt_zero_iff
#print axioms high_word
#print axioms tiny_sin
#print axioms sin_within
#print axioms cos_within

end Verified.Examples.TrigSinCos
