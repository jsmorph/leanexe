import Library.Numerics.Float64.Sinh.SinhWords
import LeanExe.ProofKit.F64NearestHalve

/-!
`Sinh.cosh` within one step of `cosh x` for `22 ≤ abs(x) ≤ 709.7827`, where the code returns
`0.5 exp abs(x)`.  The half of `exp abs(x)` is the nearest word to a real within `u/64 exp abs(x)`
of `exp abs(x) / 2` (`half_exp_near`): below 512 by `F64NearestHalve.nearest_halve` applied to
`Library.Numerics.Float64.Exp.ExpTightFloat.exp_near`, and from 512 on by scaling the word of `Library.Numerics.Float64.Exp.ExpTightFloat.positive_near`
by `2 ^ 1008`.  `cosh x` and `sinh x` differ from `exp abs(x) / 2` by at most `exp (-22)/2`,
which is below `u/64 exp abs(x)`, so the result lies within `u/16` of the target relative to it
(`large_within`), and `F64NearestRelative.within_rel_k` gives one step.
-/

namespace Library.Numerics.Float64.Sinh.CoshLarge
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhWords

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem nearest_congr (s : ℝ) (c c' : UInt64) (hc : Nearest s c) (hl : c'.toNat < limit)
    (hv : value c' = value c) : Nearest s c' :=
  ⟨hl, fun v hvl => by rw [hv]; exact hc.2 v hvl⟩

/-- The half of `exp abs(x)` for `22 ≤ abs(x) ≤ 709.7827`. -/
theorem half_exp_near (x : Float) (hxf : Finite x.toBits) (hlo : 22 ≤ |value x.toBits|)
    (hhi : |value x.toBits| ≤ 7097827 / 10 ^ 4) :
    ∃ V : ℝ, Nearest V (Wasm.IEEE64.mul Library.Numerics.Float64.Tanh.Expm1Words.half (Exp.exp x.abs).toBits) ∧
      |V - Real.exp |value x.toBits| / 2| ≤ u / 64 * Real.exp |value x.toBits| := by
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨haf, hav⟩ := abs_float x hxf
  generalize hA : |value x.toBits| = A at hlo hhi hav ⊢
  have hE1 : 1 ≤ Real.exp A := Real.one_le_exp (by linarith)
  by_cases h512 : A < 512
  · obtain ⟨se, hn, he⟩ := Library.Numerics.Float64.Exp.ExpTightFloat.exp_near x.abs haf (by rw [hav]; linarith)
      (by rw [hav]; linarith)
    rw [hav] at he
    have hE2 : Real.exp A ≤ 2 ^ 739 := Library.Numerics.Float64.Exp.ExpTightFloat.exp_le_two_pow A 739 (by push_cast; linarith)
    obtain ⟨hse1, hse2⟩ := abs_le.mp he
    rw [hu] at hse1 hse2
    obtain ⟨-, -, hnear⟩ := F64NearestHalve.nearest_halve se _ hn
      (by linarith [show (1 : ℝ) / 2 ^ 1020 ≤ 1 / 2 by norm_num])
      (by linarith [show (2 : ℝ) ^ 739 * 2 ≤ 2 ^ 1022 by norm_num])
    rw [← half_eq] at hnear
    refine ⟨se / 2, hnear, ?_⟩
    rw [← sub_div, abs_div, abs_two]
    calc |se - Real.exp A| / 2 ≤ u / 32 * Real.exp A / 2 := by gcongr
      _ = u / 64 * Real.exp A := by ring
  · push Not at h512
    obtain ⟨y, sY, hn, he, hTf, hTv, -⟩ := Library.Numerics.Float64.Exp.ExpTightFloat.positive_near x.abs haf
      (by rw [hav]; exact h512) (by rw [hav]; exact hhi)
    rw [hav] at he
    generalize (Exp.exp x.abs).toBits = T at hTf hTv ⊢
    have hEu := Library.Numerics.Float64.Exp.ExpTightFloat.exp_upper A hhi
    have hE512 : 1 / 2 ^ 1009 ≤ Real.exp A / 2 ^ 1009 := by gcongr
    obtain ⟨hs1, hs2⟩ := abs_le.mp he
    rw [hu] at hs1 hs2
    have hyr := F64NearestHalf.nearest_relative sY y hn (by linarith) (by linarith)
    obtain ⟨hy1, hy2⟩ := abs_le.mp hyr
    rw [hu] at hy1 hy2
    have hysign := (nearest_finite sY y hn).2
    have hye : Wasm.IEEE64.exponent y + 1008 < 2047 := by
      by_contra hc
      have hv := F64Magnitude.value_ge_of_exponent y 1039 16 (by norm_num) (by norm_num)
        (by norm_num) hysign (by omega)
      norm_num at hv
      linarith
    obtain ⟨-, hc'v, hc'n⟩ := F64NearestScale.scale_nearest sY y 1008 (by norm_num)
      (by norm_num) hn (by linarith) hye
    have hypos : 1 / 2 ^ 1010 ≤ value y := by linarith
    have hTlo : 1 / 2 ^ 1021 ≤ value T := by
      rw [hTv]
      linarith
    obtain ⟨hcf, hcv⟩ := mul_half T hTf hTlo
    have hcv' : value (Wasm.IEEE64.mul Library.Numerics.Float64.Tanh.Expm1Words.half T) =
        value (Wasm.IEEE64.mul y (Wasm.IEEE64.encodeFinite false (1023 + 1008) 0)) := by
      rw [hcv, hc'v, hTv]
      ring
    have hcl := F64PositiveOrder.positive_finite_encoding _ hcf (by
      rw [hcv', hc'v]
      have : (0 : ℝ) < 1 / 2 ^ 1010 := by positivity
      have : 0 < value y := by linarith
      positivity)
    refine ⟨2 ^ 1008 * sY, nearest_congr _ _ _ hc'n hcl hcv', ?_⟩
    have hid : (2 : ℝ) ^ 1008 * sY - Real.exp A / 2 =
        2 ^ 1008 * (sY - Real.exp A / 2 ^ 1009) := by
      field_simp
    rw [hid, abs_mul, abs_of_pos (by positivity)]
    calc (2 : ℝ) ^ 1008 * |sY - Real.exp A / 2 ^ 1009| ≤
        2 ^ 1008 * (u / 32 * (Real.exp A / 2 ^ 1009)) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = u / 64 * Real.exp A := by field_simp; ring

/-- One step for a target within `exp (-A)/2` of `exp A / 2` from a real within `u/64 exp A` of
`exp A / 2`. -/
theorem large_within (A y V : ℝ) (c : UInt64) (hA : 22 ≤ A) (hA' : A ≤ 7097827 / 10 ^ 4)
    (hy : |y - Real.exp A / 2| ≤ Real.exp (-A) / 2) (hc : Nearest V c)
    (hV : |V - Real.exp A / 2| ≤ u / 64 * Real.exp A) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hEu := Library.Numerics.Float64.Exp.ExpTightFloat.exp_upper A hA'
  have hEi : Real.exp (-A) ≤ 1 / 2 ^ 31 :=
    Library.Numerics.Float64.Exp.ExpTightFloat.exp_le_inv_two_pow (-A) 31 (by push_cast; linarith)
  have hprod : Real.exp A * Real.exp (-A) = 1 := by rw [← Real.exp_add]; simp
  have hE0 := Real.exp_pos A
  have hE31 : 2 ^ 31 ≤ Real.exp A := by
    nlinarith [mul_le_mul_of_nonneg_left hEi hE0.le]
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  obtain ⟨hV1, hV2⟩ := abs_le.mp hV
  rw [hu] at hV1 hV2
  have hth : F64PositiveRounding.overflowThreshold = 2 ^ 1024 - 2 ^ 970 := rfl
  have hEi' : Real.exp (-A) / 2 ≤ 1 / 2 ^ 60 * Real.exp A := by
    have : (1 : ℝ) / 2 ^ 31 / 2 ≤ 1 / 2 ^ 60 * 2 ^ 31 := by norm_num
    linarith
  have hmin : Real.exp A / 2 * (1 - 1 / 2 ^ 57) ≤ min y V := le_min (by linarith) (by linarith)
  refine F64NearestRelative.within_rel_k 1 le_rfl y V c ?_ ?_ hc ?_
  · refine le_trans ?_ hmin
    have : (1 : ℝ) / 2 ^ 1022 ≤ 2 ^ 31 / 2 * (1 - 1 / 2 ^ 57) := by norm_num
    nlinarith
  · rw [hth]
    have : (2 : ℝ) ^ 1024 * (1 - 1 / 10 ^ 5) / 2 * (1 + 1 / 2 ^ 57) < 2 ^ 1024 - 2 ^ 970 := by
      norm_num
    apply max_lt <;> linarith
  · simp only [Nat.cast_one, one_mul]
    rw [hu]
    have h1 : |V - y| ≤ 1 / 2 ^ 53 / 32 * Real.exp A := by
      rw [abs_le]
      constructor <;> linarith
    calc |V - y| ≤ 1 / 2 ^ 53 / 32 * Real.exp A := h1
      _ ≤ (1 - 1 / 2 ^ 50) * (1 / 2 ^ 53) * (Real.exp A / 2 * (1 - 1 / 2 ^ 57)) := by
          linarith
      _ ≤ (1 - 1 / 2 ^ 50) * (1 / 2 ^ 53) * min y V :=
          mul_le_mul_of_nonneg_left hmin (by norm_num)

theorem cosh_large (x : Float) (hxf : Finite x.toBits) (hlo : 22 ≤ |value x.toBits|)
    (hhi : |value x.toBits| ≤ 7097827 / 10 ^ 4) :
    F64SignedRounding.WithinSteps 1 (Real.cosh (value x.toBits)) (0.5 * Exp.exp x.abs).toBits := by
  obtain ⟨V, hn, hV⟩ := half_exp_near x hxf hlo hhi
  rw [F64Bits.toBits_mul, half_bits, ← Real.cosh_abs]
  refine large_within _ _ V _ hlo hhi ?_ hn hV
  rw [Real.cosh_eq, show (Real.exp |value x.toBits| + Real.exp (-|value x.toBits|)) / 2 -
    Real.exp |value x.toBits| / 2 = Real.exp (-|value x.toBits|) / 2 by ring,
    abs_of_pos (by positivity)]

#print axioms half_exp_near
#print axioms large_within
#print axioms cosh_large

end Library.Numerics.Float64.Sinh.CoshLarge
