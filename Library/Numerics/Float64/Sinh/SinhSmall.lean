import Library.Numerics.Float64.Sinh.SinhCore
import Library.Numerics.Float64.Sinh.SinhExpm1
import Library.Numerics.Float64.Sinh.CoshSmall
import Mathlib.Analysis.Complex.ExponentialBounds
import Library.Numerics.Float64.Sinh.SinhSign

/-!
`Sinh.sinh` within three steps of `sinh x` for `2 ^ -28 ≤ abs(x) < 1`, where the code returns
`0.5 (2 t - t t/(t + 1))` with `t = expm1 abs(x)`.  `small_steps` takes any bound `E` on the
error of `t` that keeps the relative error of the exact difference below `2.9375 u`
(`F64NearestRelative.within_rel_of`).  `sinh_small_pos` supplies `E` on nine intervals of
`τ = exp abs(x) - 1`: `2 u τ` on the path without reduction, and on the path `k = 1` the bounds of
`SinhExpm1.near_one_pos` plus the half spacing of `t`, checked by `SinhCore.check_small`.  Two
steps are out of reach of these bounds between `0.347` and `0.481`, where the relative error
reaches `2.55 u`.
-/

namespace Library.Numerics.Float64.Sinh.SinhSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhWords SinhCore

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- The words of `0.5 (2 t - t t/(t + 1))` for `2 ^ -30 ≤ t ≤ 2`: the result is a nearest word to
half of `2 t - q`, and `q` lies within `3.1 u` of `t t/(1 + t)`. -/
theorem small_words (t : UInt64) (htf : Finite t) (hT0 : 1 / 2 ^ 30 ≤ value t)
    (hT2 : value t ≤ 2) :
    ∃ qv : ℝ, |qv - value t * value t / (1 + value t)| ≤
        31 / 10 * u * (value t * value t / (1 + value t)) ∧
      value t ≤ 2 * value t - qv ∧
      Nearest ((2 * value t - qv) / 2) (Wasm.IEEE64.mul Library.Numerics.Float64.Tanh.Expm1Words.half
        (Wasm.IEEE64.sub (Wasm.IEEE64.mul Library.Numerics.Float64.Tanh.Expm1Words.two t)
          (Wasm.IEEE64.div (Wasm.IEEE64.mul t t) (Wasm.IEEE64.add t Library.Numerics.Float64.Tanh.Expm1Words.one)))) ∧
      Finite (Wasm.IEEE64.sub (Wasm.IEEE64.mul Library.Numerics.Float64.Tanh.Expm1Words.two t)
          (Wasm.IEEE64.div (Wasm.IEEE64.mul t t) (Wasm.IEEE64.add t Library.Numerics.Float64.Tanh.Expm1Words.one))) ∧
      1 / 2 ^ 1021 ≤ value (Wasm.IEEE64.sub (Wasm.IEEE64.mul Library.Numerics.Float64.Tanh.Expm1Words.two t)
          (Wasm.IEEE64.div (Wasm.IEEE64.mul t t) (Wasm.IEEE64.add t Library.Numerics.Float64.Tanh.Expm1Words.one))) := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  set T := value t with hTdef
  have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hT0
  have hone := Library.Numerics.Float64.Tanh.Expm1KernelInner.const_values.1
  have hcf := Library.Numerics.Float64.Tanh.Expm1KernelInner.const_finite.1
  have hTT : T * T ≤ 4 := by nlinarith
  obtain ⟨h2f, h2v⟩ := Library.Numerics.Float64.Tanh.TanhWords.double_value t htf
    (by rw [abs_of_pos hTpos]; linarith [show (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 30 by norm_num])
    (by rw [abs_of_pos hTpos]; linarith)
  obtain ⟨hpf, hp⟩ := F64MulBounds.mul_real_mixed t t htf htf (by
    rw [abs_of_pos (mul_pos hTpos hTpos)]
    linarith [show (4 : ℝ) < 2 ^ 1022 by norm_num])
  obtain ⟨hdf, hd⟩ := F64AddBounds.add_real_relative t _ htf hcf (by
    rw [hone, abs_of_pos (by linarith)]
    linarith [show (3 : ℝ) < 2 ^ 1023 by norm_num])
  rw [hone, add_comm (value t) 1] at hd
  set d := Wasm.IEEE64.add t Library.Numerics.Float64.Tanh.Expm1Words.one
  set p := Wasm.IEEE64.mul t t
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  rw [abs_of_pos (by linarith : (0 : ℝ) < 1 + T), hu] at hd1 hd2
  have hdpos : 1 / 2 ≤ value d := by linarith
  obtain ⟨hp1, hp2⟩ := abs_le.mp hp
  rw [abs_of_pos (mul_pos hTpos hTpos), hu, hη] at hp1 hp2
  have hpb : |value p| ≤ 5 := by rw [abs_le]; constructor <;> linarith
  have hpd : |value p / value d| < 2 ^ 1022 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < value d), div_lt_iff₀ (by linarith)]
    have : (5 : ℝ) < 2 ^ 1022 * (1 / 2) := by norm_num
    nlinarith
  obtain ⟨hqf, hq⟩ := F64DivBounds.div_real_mixed p d hpf hdf
    (CoshSmall.magnitude_ne_zero d (by linarith)) hpd
  set q := Wasm.IEEE64.div p d
  have hqr := small_round T (value p) (value d) (value q) hT0 hT2 hp hd hq
  have hQ1 : T * T / (1 + T) ≤ T := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hQ2 : T * T / (1 + T) ≤ 2 / 3 * T := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hQ0 : 0 ≤ T * T / (1 + T) := by positivity
  obtain ⟨hqr1, hqr2⟩ := abs_le.mp hqr
  have hc31 : 31 / 10 * u * (T * T / (1 + T)) ≤ 1 / 2 ^ 40 * T := by
    rw [hu]
    have := mul_le_mul_of_nonneg_left hQ1 (by positivity : (0 : ℝ) ≤ 31 / 10 * (1 / 2 ^ 53))
    have h2 : 31 / 10 * (1 / 2 ^ 53) * T ≤ 1 / 2 ^ 40 * T :=
      mul_le_mul_of_nonneg_right (by norm_num) hTpos.le
    linarith
  have hV0 : T ≤ 2 * T - value q := by linarith
  have hvn := F64NearestSum.sub_nearest _ q h2f hqf (by rw [h2v]; linarith)
    (by rw [h2v]; linarith [show (4 : ℝ) < 2 ^ 1023 by norm_num])
  rw [h2v] at hvn
  obtain ⟨-, -, hcn⟩ := F64NearestHalve.nearest_halve _ _ hvn
    (by linarith [show (1 : ℝ) / 2 ^ 1020 ≤ 1 / 2 ^ 30 by norm_num])
    (by linarith [show (4 : ℝ) ≤ 2 ^ 1022 by norm_num])
  rw [← half_eq] at hcn
  have hvr := F64NearestHalf.nearest_relative _ _ hvn
    (by linarith [show (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 30 by norm_num])
    (by linarith [show (4 : ℝ) < 2 ^ 1022 by norm_num])
  obtain ⟨hvr1, -⟩ := abs_le.mp hvr
  rw [hu] at hvr1
  refine ⟨value q, hqr, hV0, hcn, (nearest_finite _ _ hvn).1, ?_⟩
  have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 ^ 30 * (1 - 1 / 2 ^ 53) := by norm_num
  nlinarith

/-- The value of `0.5 (2 t - t t/(t + 1))` within three steps, from a bound `E` on `t`. -/
theorem small_steps (x : Float) (hlo : 1 / 2 ^ 28 ≤ |value x.toBits|)
    (hhi : |value x.toBits| < 1) (E : ℝ) (htf : Finite (Tanh.expm1 x.abs).toBits)
    (hT : |value (Tanh.expm1 x.abs).toBits - (Real.exp |value x.toBits| - 1)| ≤ E)
    (hE : E ≤ (Real.exp |value x.toBits| - 1) / 2 ^ 40)
    (hnum : E * (1 + 1 / ((1 + value (Tanh.expm1 x.abs).toBits) *
        (1 + (Real.exp |value x.toBits| - 1)))) +
      31 / 10 * u * (value (Tanh.expm1 x.abs).toBits * value (Tanh.expm1 x.abs).toBits /
        (1 + value (Tanh.expm1 x.abs).toBits)) ≤
      2.9375 * u * ((Real.exp |value x.toBits| - 1) +
        (Real.exp |value x.toBits| - 1) / (1 + (Real.exp |value x.toBits| - 1)))) :
    F64SignedRounding.WithinSteps 3 (Real.sinh |value x.toBits|)
      (0.5 * (2.0 * Tanh.expm1 x.abs - Tanh.expm1 x.abs * Tanh.expm1 x.abs /
        (Tanh.expm1 x.abs + 1.0))).toBits ∧
    F64SignedRounding.WithinSteps 3 (-Real.sinh |value x.toBits|)
      (-0.5 * (2.0 * Tanh.expm1 x.abs - Tanh.expm1 x.abs * Tanh.expm1 x.abs /
        (Tanh.expm1 x.abs + 1.0))).toBits := by
  generalize hA : |value x.toBits| = A at hlo hhi hT hE hnum ⊢
  simp only [F64Bits.toBits_mul, F64Bits.toBits_sub, F64Bits.toBits_div, F64Bits.toBits_add,
    half_bits, SinhSign.neg_half_bits, Library.Numerics.Float64.Tanh.TanhTheorem.two_bits, Library.Numerics.Float64.Tanh.TanhTheorem.one_bits]
  generalize (Tanh.expm1 x.abs).toBits = t at htf hT hE hnum ⊢
  set τ := Real.exp A - 1 with hτdef
  set T := value t with hTdef
  have hτA : A ≤ τ := by rw [hτdef]; linarith [Real.add_one_le_exp A]
  have hτ1 : τ ≤ 172 / 100 := by
    have h1 : Real.exp A ≤ Real.exp 1 := Real.exp_le_exp.mpr hhi.le
    have h2 := Real.exp_one_lt_d9
    rw [hτdef]; norm_num at h2; linarith
  have hτ0 : 1 / 2 ^ 28 ≤ τ := hlo.trans hτA
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  have hT0 : 1 / 2 ^ 30 ≤ T := by
    have : (1 : ℝ) / 2 ^ 30 ≤ 1 / 2 ^ 28 * (1 - 1 / 2 ^ 40) := by norm_num
    linarith
  have hT2' : T ≤ 2 := by linarith
  obtain ⟨qv, hqr, hV0, hcn, hvf, hvlo⟩ := small_words t htf hT0 hT2'
  rw [SinhSign.mul_negHalf _ hvf hvlo, F64SignedRounding.within_negate, and_self]
  have hy : Real.sinh A = (τ + τ / (1 + τ)) / 2 := by
    have := two_sinh A
    rw [← hτdef] at this
    linarith
  have hf := f_diff T τ (by linarith) (by linarith)
  have herr : |(2 * T - qv) - (τ + τ / (1 + τ))| ≤ 2.9375 * u * (τ + τ / (1 + τ)) := by
    have hsplit : (2 * T - qv) - (τ + τ / (1 + τ)) =
        ((T + T / (1 + T)) - (τ + τ / (1 + τ))) - (qv - T * T / (1 + T)) := by
      have : (1 : ℝ) + T ≠ 0 := by linarith
      field_simp; ring
    rw [hsplit, hf]
    have h1 : |(T - τ) * (1 + 1 / ((1 + T) * (1 + τ)))| ≤
        E * (1 + 1 / ((1 + T) * (1 + τ))) := by
      have hpos : (0 : ℝ) < 1 + 1 / ((1 + T) * (1 + τ)) := by
        have : 0 < (1 + T) * (1 + τ) := by nlinarith
        positivity
      rw [abs_mul, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_right hT hpos.le
    calc |(T - τ) * (1 + 1 / ((1 + T) * (1 + τ))) - (qv - T * T / (1 + T))| ≤
        |(T - τ) * (1 + 1 / ((1 + T) * (1 + τ)))| + |qv - T * T / (1 + T)| := abs_sub _ _
      _ ≤ E * (1 + 1 / ((1 + T) * (1 + τ))) + 31 / 10 * u * (T * T / (1 + T)) :=
          add_le_add h1 hqr
      _ ≤ _ := hnum
  have hfτ : 0 ≤ τ / (1 + τ) := by positivity
  refine F64NearestRelative.within_rel_of 3 (by norm_num) (by norm_num) _ _ _ ?_ ?_ hcn ?_
  · rw [hy]
    have : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 ^ 28 / 2 := by norm_num
    linarith
  · rw [hy]
    have : τ / (1 + τ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith [show (4 : ℝ) < 2 ^ 1022 by norm_num]
  · rw [hy, show (2 * T - qv) / 2 - (τ + τ / (1 + τ)) / 2 =
      ((2 * T - qv) - (τ + τ / (1 + τ))) / 2 by ring, abs_div, abs_two]
    push_cast
    have h2 : (2.9375 : ℝ) = 3 - 1 / 16 := by norm_num
    rw [h2] at herr
    linarith

#print axioms small_words
#print axioms small_steps

end Library.Numerics.Float64.Sinh.SinhSmall
