import Library.Numerics.Float64.Tanh.Expm1KernelOuter
import Library.Numerics.Float64.Tanh.Expm1SubOne
import LeanExe.ProofKit.F64NearestScale

/-!
Facts shared by the five scaling forms of fdlibm's `expm1`.  `common` takes the kernel's inputs
`y` and `c` for a reduced argument `r` within `2 ^ -70` of `value y + value c` and bounds
`value y - e2` by `0.2401 u` from `exp r - 1`, with the range of `exp r`.  `within_of_level` is
the one-step criterion that the forms use: a nearest word of `s` is within one step of the
reference of `y` when `y` lies at least two spacings into binade `e` and `abs(s - y)` is below the
spacing of that binade.
-/

namespace Library.Numerics.Float64.Tanh.Expm1FormBase
open CodeLib.IEEE64 LeanExe.ProofKit Expm1KernelInner Expm1KernelOuter

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

theorem expCoeffs_eight :
    TaylorRemainder.expCoeffs 8 = [1, 1, 1 / 2, 1 / 6, 1 / 24, 1 / 120, 1 / 720, 1 / 5040] := by
  decide +kernel

/-- The exponential on `[-0.34661, 0.34661]` lies in `[0.7070, 1.4143]`. -/
theorem exp_range (r : ℝ) (hr : |r| ≤ 34661 / 100000) :
    7070 / 10000 ≤ Real.exp r ∧ Real.exp r ≤ 14143 / 10000 := by
  have hb := abs_le.mp hr
  have hup := TaylorRemainder.exp_remainder (34661 / 100000) (by norm_num) 8 (by norm_num)
  have hlo := TaylorRemainder.exp_remainder (-(34661 / 100000)) (by norm_num) 8 (by norm_num)
  rw [expCoeffs_eight] at hup hlo
  simp only [PolyBound.eval_cons, PolyBound.eval_nil] at hup hlo
  norm_num [Nat.factorial] at hup hlo
  constructor
  · calc (7070 / 10000 : ℝ) ≤ Real.exp (-(34661 / 100000)) := by
          have := (abs_le.mp hlo).1
          linarith
      _ ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith)
  · calc Real.exp r ≤ Real.exp (34661 / 100000) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 14143 / 10000 := by
          have := (abs_le.mp hup).2
          linarith

/-- The kernel's facts for a reduced argument `r`. -/
theorem common (y c : UInt64) (hyf : Finite y) (hcf : Finite c) (hy : |value y| ≤ 3466 / 10000)
    (hc : |value c| ≤ 36 / 100 * u) (r : ℝ) (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) :
    Finite (Expm1Words.e2 y c) ∧ |value (Expm1Words.e2 y c)| ≤ 7 / 100 ∧
      |(value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)| ≤ 2401 / 10000 * u ∧
      |r| ≤ 34661 / 100000 ∧ 7070 / 10000 ≤ Real.exp r ∧ Real.exp r ≤ 14143 / 10000 := by
  obtain ⟨hf, he, hm⟩ := e2_spec y c hyf hcf hy hc
  have hu : u = 1 / 2 ^ 53 := u_value
  have hr' : |r| ≤ 34661 / 100000 := by
    have h1 := abs_sub_abs_le_abs_sub r (value y + value c)
    rw [abs_sub_comm] at h1
    have h2 := abs_add_le (value y) (value c)
    have h3 : 36 / 100 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    have h4 : (1 : ℝ) / 2 ^ 70 ≤ 1 / 10 ^ 10 := by norm_num
    linarith
  obtain ⟨hlo, hhi⟩ := exp_range r hr'
  refine ⟨hf, hm, ?_, hr', hlo, hhi⟩
  have hd : |Real.exp (value y + value c) - Real.exp r| ≤ 14143 / 10000 * (2 * (1 / 2 ^ 70)) := by
    rw [show value y + value c = r + (value y + value c - r) by ring, Real.exp_add,
      show Real.exp r * Real.exp (value y + value c - r) - Real.exp r =
        Real.exp r * (Real.exp (value y + value c - r) - 1) by ring, abs_mul,
      abs_of_pos (Real.exp_pos r)]
    have h1 := Real.abs_exp_sub_one_le (hr.trans (by norm_num))
    exact mul_le_mul hhi (h1.trans (by linarith)) (abs_nonneg _) (by norm_num)
  calc |(value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1)| ≤
      |(value y - value (Expm1Words.e2 y c)) - (Real.exp (value y + value c) - 1)| +
        |Real.exp (value y + value c) - Real.exp r| := by
        rw [show (value y - value (Expm1Words.e2 y c)) - (Real.exp r - 1) =
          ((value y - value (Expm1Words.e2 y c)) - (Real.exp (value y + value c) - 1)) +
            (Real.exp (value y + value c) - Real.exp r) by ring]
        exact abs_add_le _ _
    _ ≤ 24 / 100 * u + 14143 / 10000 * (2 * (1 / 2 ^ 70)) := add_le_add he hd
    _ ≤ 2401 / 10000 * u := by rw [hu]; norm_num

/-- The one-step criterion of the forms. -/
theorem within_of_level (y s : ℝ) (c : UInt64) (e : Nat) (he : 1 ≤ e) (he' : e ≤ 2046)
    (hy : ((2 : ℝ) ^ (e + 51) + 2 * 2 ^ (e - 1)) / 2 ^ 1074 ≤ y)
    (hyt : y < F64PositiveRounding.overflowThreshold)
    (hc : F64NearestNonnegative.Nearest s c) (hd : |s - y| < (2 : ℝ) ^ (e - 1) / 2 ^ 1074) :
    F64SignedRounding.WithinSteps 1 y c := by
  by_cases htop : (2 : ℝ) ^ (e + 52) / 2 ^ 1074 ≤ y
  · have he2 : e + 1 ≤ 2046 := by
      by_contra hn
      have : e = 2046 := by omega
      subst this
      have hth : F64PositiveRounding.overflowThreshold < (2 : ℝ) ^ (2046 + 52) / 2 ^ 1074 := by
        unfold F64PositiveRounding.overflowThreshold; norm_num
      linarith
    refine F64NearestSteps.within_of_half y s c (e + 1) (by omega) he2
      (by rw [show e + 1 + 51 = e + 52 by omega]; exact htop) hyt hc ?_
    rw [show e + 1 - 1 = e by omega]
    have : (2 : ℝ) ^ e / 2 ^ 1074 / 2 = 2 ^ (e - 1) / 2 ^ 1074 := by
      have h2 : (2 : ℝ) ^ e = 2 ^ (e - 1) * 2 := by
        rw [← pow_succ, show e - 1 + 1 = e by omega]
      rw [h2]; ring
    rw [this]; exact hd
  · exact F64NearestSteps.within_of_interior y s c e he he' hy hyt hc hd

#print axioms exp_range
#print axioms common
#print axioms within_of_level

end Library.Numerics.Float64.Tanh.Expm1FormBase
