import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace LeanExe.ProofKit.RealExpError

theorem taylor_error_one (x : ℝ) (hx : |x| ≤ 1) (n : Nat) (hn : 0 < n) :
    |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ)| ≤
      (n + 1 : ℝ) / (n.factorial * n) := by
  have hp : |x| ^ n ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) ^ n := by gcongr
      _ = 1 := one_pow n
  calc
    _ ≤ |x| ^ n * ((n + 1 : ℝ) / (n.factorial * n)) := by
      simpa only [Nat.cast_succ] using Real.exp_bound hx hn
    _ ≤ 1 * ((n + 1 : ℝ) / (n.factorial * n)) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (n + 1 : ℝ) / (n.factorial * n) := one_mul _

theorem taylor_five_error (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120)| ≤
      |x| ^ 6 * (7 / 4320) := by
  have hsum : (∑ m ∈ Finset.range 6, x ^ m / (m.factorial : ℝ)) =
      1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have h := Real.exp_bound hx (n := 6) (by decide)
  rw [hsum] at h
  norm_num [Nat.factorial] at h
  exact h

theorem taylor_five_error_small (x : ℝ) (hx : |x| ≤ 1 / 256) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120)| ≤
      7 / (2 : ℝ) ^ 60 := by
  have hx1 : |x| ≤ 1 := hx.trans (by norm_num)
  have hpow : |x| ^ 6 ≤ (1 / 256 : ℝ) ^ 6 := by
    gcongr
  calc
    _ ≤ |x| ^ 6 * (7 / 4320) := taylor_five_error x hx1
    _ ≤ (1 / 256 : ℝ) ^ 6 * (7 / 4320) := by
      exact mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ ≤ 7 / (2 : ℝ) ^ 60 := by norm_num

theorem exp_perturbation_small (a b : ℝ) (ha : |a| ≤ 1 / 256)
    (hab : |b - a| ≤ 1 / 256) :
    |Real.exp b - Real.exp a| ≤ 2 * |b - a| := by
  have ha1 : |a| ≤ 1 := ha.trans (by norm_num)
  have hab1 : |b - a| ≤ 1 := hab.trans (by norm_num)
  have he := Real.exp_bound ha1 (n := 1) (by decide)
  norm_num [Finset.sum_range_succ] at he
  have hea : Real.exp a ≤ 129 / 128 := by
    have h := (le_abs_self (Real.exp a - 1)).trans he
    linarith
  have ht := Real.abs_exp_sub_one_sub_id_le hab1
  have hphi : |Real.exp (b - a) - 1| ≤ (257 / 256) * |b - a| := by
    have hsq : |b - a| ^ 2 ≤ (1 / 256) * |b - a| := by
      simpa only [sq] using mul_le_mul_of_nonneg_right hab (abs_nonneg (b - a))
    have htriangle := abs_add_le (Real.exp (b - a) - 1 - (b - a)) (b - a)
    rw [sub_add_cancel] at htriangle
    rw [← sq_abs] at ht
    linarith
  have hid : Real.exp b - Real.exp a =
      Real.exp a * (Real.exp (b - a) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add, show a + (b - a) = b by ring]
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos a)]
  calc
    _ ≤ (129 / 128) * ((257 / 256) * |b - a|) :=
      mul_le_mul hea hphi (abs_nonneg _) (by norm_num)
    _ ≤ 2 * |b - a| := by nlinarith [abs_nonneg (b - a)]

#print axioms exp_perturbation_small
#print axioms taylor_error_one
#print axioms taylor_five_error
#print axioms taylor_five_error_small

end LeanExe.ProofKit.RealExpError
