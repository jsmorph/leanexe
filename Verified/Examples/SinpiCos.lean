import Verified.Examples.SinpiSin

/-!
`Sinpi.cospi`: within one step of `cos (π x)` for every finite `x`.  Below `2 ^ -29` the result
is 1, within `2 ^ -55` of `cos (π x)`.  Below 1 the cosine pieces run on `|x|`, with `+0` at
`|x| = 1/2`.  From 1 below `2 ^ 52` they run on the fraction of `|x|`, with `+0` at an integer
plus `1/2` and `±1` at an integer.  From `2 ^ 52` on the result is `±1` by the parity of the
integer `|x|`.
-/

namespace Verified.Examples.SinpiCos

open CodeLib.IEEE64 LeanExe.ProofKit TrigSinCos TanBigWords TanTrunc TanWith SinpiBits
  SinpiFloor SinpiPieces SinpiCommon SinpiReflect SinpiSin SinpiKernels SinpiTanKernel

set_option exponentiation.threshold 1200

theorem cos_shift (F : ℝ) (N : Nat) :
    Real.cos (Real.pi * (N + F)) = if N % 2 = 1 then -Real.cos (Real.pi * F)
      else Real.cos (Real.pi * F) := by
  rw [show Real.pi * (N + F) = Real.pi * F + N * Real.pi by ring, Real.cos_add_nat_mul_pi]
  split_ifs with h
  · rw [Odd.neg_one_pow (Nat.odd_iff.mpr h)]; ring
  · rw [Even.neg_one_pow (Nat.even_iff.mpr (by omega))]; ring

theorem cos_abs_pi (v : ℝ) : Real.cos (Real.pi * v) = Real.cos (Real.pi * |v|) := by
  rcases le_or_gt 0 v with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, show Real.pi * -v = -(Real.pi * v) by ring, Real.cos_neg]

/-- The word of 1 is within one step of a number within `2 ^ -55` of 1. -/
theorem one_near (y : ℝ) (h : |1 - y| ≤ 1 / 2 ^ 55) :
    F64SignedRounding.WithinSteps 1 y 0x3FF0000000000000 := by
  obtain ⟨-, -, -, -, -, v1, -, -, f1⟩ := quarter_facts
  have h' := abs_le.mp h
  have hy : 1 / 2 ≤ |y| := by rw [abs_of_pos (by linarith)]; linarith
  refine TanStep.near_rel _ 1 y f1 (fun v _ => by rw [v1, sub_self, abs_zero]; exact abs_nonneg _)
    (le_trans (by norm_num) hy) ?_ ?_
  · rw [abs_of_pos (by linarith)]; linarith [show (1 : ℝ) + 1 ≤ 2 ^ 1000 by norm_num]
  · rw [abs_of_pos (show (0 : ℝ) < y by linarith), show unitRoundoff64 = 1 / 2 ^ 53 from rfl]
    have : (1 : ℝ) / 2 ^ 55 ≤ 74 / 100 * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 55) := by norm_num
    linarith [h'.2]

/-- A word with an exact value of `±1` is within one step of it. -/
theorem pm_one (c : UInt64) (y : ℝ) (hcf : Finite c) (hc : value c = y) (hy : |y| = 1) :
    F64SignedRounding.WithinSteps 1 y c :=
  exact_within c y hcf hc (by rw [hy]; norm_num) (by rw [hy]; norm_num)

theorem one_negOne : (1.0 : Float).toBits = 0x3FF0000000000000 ∧
    (-1.0 : Float).toBits = 0xBFF0000000000000 ∧ value (0xBFF0000000000000 : UInt64) = -1 ∧
    Finite (0xBFF0000000000000 : UInt64) := by
  refine ⟨by decide, ?_, ?_, by unfold CodeLib.IEEE64.Finite; decide⟩
  · rw [F64Bits.toBits_neg, show (1.0 : Float).toBits = 0x3FF0000000000000 by decide]
    decide +kernel
  · exact TanOdd.value_negOne

/-- `cos (π x)` within `2 ^ -55` of 1 below `2 ^ -29`. -/
theorem cos_tiny (v : ℝ) (h : |v| < 1 / 2 ^ 29) :
    |1 - Real.cos (Real.pi * v)| ≤ 1 / 2 ^ 55 := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := Real.pi * v)
  have h2 := Real.cos_le_one (Real.pi * v)
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have hv2 : (Real.pi * v) ^ 2 ≤ (3.15 * (1 / 2 ^ 29)) ^ 2 := by
    rw [← sq_abs, abs_mul, abs_of_pos hpi0]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul hpi.le h.le (abs_nonneg _) (by norm_num)) 2
  rw [abs_of_nonneg (by linarith)]
  have : (3.15 * (1 / 2 ^ 29) : ℝ) ^ 2 / 2 ≤ 1 / 2 ^ 55 := by norm_num
  linarith

/-- `cospi` below 1. -/
theorem cospi_small (x : Float) (hxf : Finite x.toBits) (h : |value x.toBits| < 1) :
    F64SignedRounding.WithinSteps 1 (Real.cos (Real.pi * value x.toBits))
      (Sinpi.cospi x).toBits := by
  obtain ⟨hs, hf, hv, -, hix, -⟩ := abs_facts x hxf
  obtain ⟨c1, c29, -, -⟩ := abs_thresholds x hxf
  obtain ⟨t1, t2, t3⟩ := thresholds x.abs _ |value x.toBits| hix hs hv
  obtain ⟨-, q5, -, -, v5, -, -, f5, -⟩ := quarter_facts
  obtain ⟨o1, -, -, -⟩ := one_negOne
  rw [cos_abs_pi]
  unfold Sinpi.cospi
  dsimp only
  rw [ax_abs, if_pos (c1.mpr h)]
  have hpcs := cos_pieces x.abs |value x.toBits| hs hf hv
  by_cases hq : |value x.toBits| < 1 / 4
  · rw [if_pos (t1.mpr hq)]
    by_cases ht : |value x.toBits| < 1 / 2 ^ 29
    · have hu0 := toUInt64_small x.abs hf (by rw [hv, abs_abs]; linarith)
      rw [if_pos (by rw [decide_eq_true (c29.mpr ht), hu0]; rfl), o1]
      exact one_near _ (cos_tiny _ (by rw [abs_abs]; exact ht))
    · rw [if_neg (by rw [decide_eq_false (fun h' => ht (c29.mp h'))]; simp)]
      exact (hpcs (le_trans (by norm_num) (not_lt.mp ht)) h).1 hq
  rw [if_neg (fun h' => hq (t1.mp h'))]
  have hA0 : 1 / 2 ^ 54 ≤ |value x.toBits| := by linarith
  by_cases h2 : |value x.toBits| < 1 / 2
  · rw [if_pos (t2.mpr h2)]
    exact (hpcs hA0 h).2.1 (not_lt.mp hq) h2
  rw [if_neg (fun h' => h2 (t2.mp h'))]
  by_cases h3 : |value x.toBits| < 3 / 4
  · rw [if_pos (t3.mpr h3)]
    by_cases hh : |value x.toBits| = 1 / 2
    · rw [if_pos ((feq_iff _ _ hf (by rw [q5]; exact f5)).mpr (by rw [hv, q5, v5, hh])), hh,
        show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.cos_pi_div_two, (zero_bits').1]
      exact F64SelfStep.zero_step _ (by decide)
    · rw [if_neg (fun h' => hh (by
        have := (feq_iff _ _ hf (by rw [q5]; exact f5)).mp h'
        rw [hv, q5, v5] at this
        exact this))]
      exact (hpcs hA0 h).2.2.1 (lt_of_le_of_ne (not_lt.mp h2) (Ne.symm hh)) h3
  rw [if_neg (fun h' => h3 (t3.mp h'))]
  exact (hpcs hA0 h).2.2.2 (not_lt.mp h3)

#print axioms cos_tiny
#print axioms cospi_small

end Verified.Examples.SinpiCos
