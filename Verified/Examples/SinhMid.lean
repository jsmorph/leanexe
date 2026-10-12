import Verified.Examples.SinhSmall

/-!
`Sinh.sinh` within three steps of `sinh x` for `1 ≤ abs(x) < 22`, where the code returns
`0.5 (t + t/(t + 1))` with `t = expm1 abs(x)`.  `mid_words` gives the result as a nearest word to
half of `t + r`, with `r` within `2.1 u` of `t/(1 + t)`; `mid_steps` takes any bound `E` on the
error of `t` that keeps the relative error below `2.9375 u`.  On the path `k = 1`, up to
`θ2 ≈ 1.0397`, `E = 1.9803 u`; above, `SinhExpm1.near_k_pos` gives `E = 1.9605 u + u τ`, or
`1.8501 u τ` with `τ ≥ 3`.
-/

namespace Verified.Examples.SinhMid
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhWords SinhCore

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem mid_words (t : UInt64) (htf : Finite t) (hT1 : 1 ≤ value t) (hT2 : value t ≤ 2 ^ 33) :
    ∃ rv : ℝ, |rv - value t / (1 + value t)| ≤ 21 / 10 * u * (value t / (1 + value t)) ∧
      0 ≤ rv ∧
      Nearest ((value t + rv) / 2) (Wasm.IEEE64.mul Expm1Words.half
        (Wasm.IEEE64.add t (Wasm.IEEE64.div t (Wasm.IEEE64.add t Expm1Words.one)))) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  set T := value t with hTdef
  have hone := Expm1KernelInner.const_values.1
  have hcf := Expm1KernelInner.const_finite.1
  obtain ⟨hdf, hd⟩ := F64AddBounds.add_real_relative t _ htf hcf (by
    rw [hone, abs_of_pos (by linarith)]
    linarith [show (2 : ℝ) ^ 33 + 1 < 2 ^ 1023 by norm_num])
  rw [hone, add_comm (value t) 1] at hd
  set d := Wasm.IEEE64.add t Expm1Words.one
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + T), hu] at hd1 hd2
  have hdpos : 1 ≤ value d := by linarith
  have hTd : |T / value d| < 2 ^ 1022 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < T), abs_of_pos (by linarith : (0 : ℝ) < value d),
      div_lt_iff₀ (by linarith)]
    nlinarith [show (2 : ℝ) ^ 33 < 2 ^ 1022 by norm_num]
  obtain ⟨hrf, hr⟩ := F64DivBounds.div_real_mixed t d htf hdf
    (CoshSmall.magnitude_ne_zero d (by linarith)) hTd
  set r := Wasm.IEEE64.div t d
  have hrr := mid_round T (value d) (value r) hT1 hd hr
  have hR1 : T / (1 + T) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hR0 : 0 ≤ T / (1 + T) := by positivity
  obtain ⟨hrr1, hrr2⟩ := abs_le.mp hrr
  rw [hu] at hrr1 hrr2
  have hr0 : 0 ≤ value r := by nlinarith
  have hwn := F64NearestSum.add_nearest t r htf hrf (by linarith)
    (by linarith [show (2 : ℝ) ^ 33 + 2 < 2 ^ 1023 by norm_num])
  set w := Wasm.IEEE64.add t r
  obtain ⟨-, -, hcn⟩ := F64NearestHalve.nearest_halve _ w hwn
    (by linarith [show (1 : ℝ) / 2 ^ 1020 ≤ 1 by norm_num])
    (by linarith [show (2 : ℝ) ^ 33 + 2 ≤ 2 ^ 1022 by norm_num])
  rw [← half_eq] at hcn
  exact ⟨value r, hrr, hr0, hcn⟩

theorem mid_steps (x : Float) (hlo : 1 ≤ |value x.toBits|) (hhi : |value x.toBits| < 22) (E : ℝ)
    (htf : Finite (Tanh.expm1 x.abs).toBits)
    (hT : |value (Tanh.expm1 x.abs).toBits - (Real.exp |value x.toBits| - 1)| ≤ E)
    (hE : E ≤ (Real.exp |value x.toBits| - 1) / 2 ^ 40)
    (hnum : E * (1 + 1 / ((1 + value (Tanh.expm1 x.abs).toBits) *
        (1 + (Real.exp |value x.toBits| - 1)))) + 21 / 10 * u ≤
      2.9375 * u * ((Real.exp |value x.toBits| - 1) +
        (Real.exp |value x.toBits| - 1) / (1 + (Real.exp |value x.toBits| - 1)))) :
    F64SignedRounding.WithinSteps 3 (Real.sinh |value x.toBits|)
      (0.5 * (Tanh.expm1 x.abs + Tanh.expm1 x.abs / (Tanh.expm1 x.abs + 1.0))).toBits := by
  have hu : u = 1 / 2 ^ 53 := rfl
  generalize hA : |value x.toBits| = A at hlo hhi hT hE hnum ⊢
  simp only [F64Bits.toBits_mul, F64Bits.toBits_div, F64Bits.toBits_add, half_bits,
    TanhTheorem.one_bits]
  generalize (Tanh.expm1 x.abs).toBits = t at htf hT hE hnum ⊢
  set τ := Real.exp A - 1 with hτdef
  set T := value t with hTdef
  have hτ1 : 1718 / 1000 ≤ τ := by
    have h1 : Real.exp 1 ≤ Real.exp A := Real.exp_le_exp.mpr hlo
    have h2 := Real.exp_one_gt_d9
    rw [hτdef]; norm_num at h2; linarith
  have hτ2 : τ ≤ 2 ^ 32 := by
    have := ExpTightFloat.exp_le_two_pow A 32 (by push_cast; linarith)
    rw [hτdef]; linarith
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  have hT0 : 1 / 2 ≤ T := by
    have : τ / 2 ^ 40 ≤ τ / 2 := by gcongr; norm_num
    linarith
  have hT1' : 1 ≤ T := by
    have h1 : τ * (1 - 1 / 2 ^ 40) ≤ T := by linarith
    by_contra h
    push Not at h
    nlinarith
  have hT2' : T ≤ 2 ^ 33 := by
    have : τ / 2 ^ 40 ≤ τ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith [show (2 : ℝ) ^ 32 + 2 ^ 32 ≤ 2 ^ 33 by norm_num]
  obtain ⟨rv, hrr, hr0, hcn⟩ := mid_words t htf hT1' hT2'
  have hy : Real.sinh A = (τ + τ / (1 + τ)) / 2 := by
    have := two_sinh A
    rw [← hτdef] at this
    linarith
  have hf := f_diff T τ (by linarith) (by linarith)
  have hR1 : T / (1 + T) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have herr : |(T + rv) - (τ + τ / (1 + τ))| ≤ 2.9375 * u * (τ + τ / (1 + τ)) := by
    have hsplit : (T + rv) - (τ + τ / (1 + τ)) =
        ((T + T / (1 + T)) - (τ + τ / (1 + τ))) + (rv - T / (1 + T)) := by ring
    rw [hsplit, hf]
    have hpos : (0 : ℝ) < 1 + 1 / ((1 + T) * (1 + τ)) := by
      have : 0 < (1 + T) * (1 + τ) := by nlinarith
      positivity
    have h1 : |(T - τ) * (1 + 1 / ((1 + T) * (1 + τ)))| ≤
        E * (1 + 1 / ((1 + T) * (1 + τ))) := by
      rw [abs_mul, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_right hT hpos.le
    have h2 : 21 / 10 * u * (T / (1 + T)) ≤ 21 / 10 * u :=
      by rw [hu]; nlinarith
    calc |(T - τ) * (1 + 1 / ((1 + T) * (1 + τ))) + (rv - T / (1 + T))| ≤
        |(T - τ) * (1 + 1 / ((1 + T) * (1 + τ)))| + |rv - T / (1 + T)| := abs_add_le _ _
      _ ≤ E * (1 + 1 / ((1 + T) * (1 + τ))) + 21 / 10 * u := by linarith
      _ ≤ _ := hnum
  have hfτ : 0 ≤ τ / (1 + τ) := by positivity
  refine F64NearestRelative.within_rel_of 3 (by norm_num) (by norm_num) _ _ _ ?_ ?_ hcn ?_
  · rw [hy]
    have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 := by norm_num
    linarith
  · rw [hy]
    have : τ / (1 + τ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith [show (2 : ℝ) ^ 32 + 1 < 2 ^ 1022 by norm_num]
  · rw [hy, show (T + rv) / 2 - (τ + τ / (1 + τ)) / 2 =
      ((T + rv) - (τ + τ / (1 + τ))) / 2 by ring, abs_div, abs_two]
    push_cast
    have h2 : (2.9375 : ℝ) = 3 - 1 / 16 := by norm_num
    rw [h2] at herr
    linarith

#print axioms mid_words
#print axioms mid_steps

end Verified.Examples.SinhMid
