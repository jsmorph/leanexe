import Project.ExpNeg.Polynomial
import Project.ProofKit.F64RelativeSquare

namespace Project.ExpNeg
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

noncomputable def errorFactor (stage : Nat) : ℝ := 63*2^stage-3

theorem errorFactor_bounds (stage : Nat) (hs : stage ≤ 6) :
    0 ≤ errorFactor stage ∧ errorFactor stage ≤ 4029 := by
  have hl : (1:ℝ) ≤ 2^stage := one_le_pow₀ (by norm_num)
  have hu : (2:ℝ)^stage ≤ 2^6 := pow_le_pow_right₀ (by norm_num) hs
  dsimp [errorFactor]
  norm_num at hu
  constructor <;> linarith

theorem power_bounds (r : ℝ) (stage : Nat) (hl : 1/3 ≤ r) (hu : r ≤ 1) (hs : stage ≤ 6) :
    (1/3:ℝ)^64 ≤ r^(2^stage) ∧ r^(2^stage) ≤ 1 := by
  have he : (2:Nat)^stage ≤ 64 := (Nat.pow_le_pow_right (by omega) hs).trans (by norm_num)
  refine ⟨?_, pow_le_one₀ (by linarith) hu⟩
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) he).trans
    (pow_le_pow_left₀ (by norm_num) hl _)

theorem square_error (steps stage : Nat) (word : UInt64) (r : ℝ)
    (hsteps : stage+steps ≤ 6) (hl : 1/3 ≤ r) (hu : r ≤ 1) (hf : Finite word)
    (he : |value word-r^(2^stage)| ≤ errorFactor stage*arithmeticEpsilon*r^(2^stage)) :
    Finite (square steps word) ∧
      |value (square steps word)-r^(2^(stage+steps))| ≤
        errorFactor (stage+steps)*arithmeticEpsilon*r^(2^(stage+steps)) := by
  induction steps generalizing stage word with
  | zero => simpa [square] using And.intro hf he
  | succ steps ih =>
    have hs : stage ≤ 6 := by omega
    have hp := power_bounds r stage hl hu hs
    have hr : 0 < r^(2^stage) := lt_of_lt_of_le (by norm_num) hp.1
    have hk := errorFactor_bounds stage hs
    have hmin : minNormal64 ≤ 2*(r^(2^stage))^2 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (1/3)^64) hp.1 2
      norm_num [minNormal64] at hh ⊢
      linarith only [hh]
    have hsq := F64Square.relative_approximation word (r^(2^stage)) (errorFactor stage)
      hf hr hp.2 hk.1 (hk.2.trans (by norm_num)) hmin he
    have hpow : (r^(2^stage))^2 = r^(2^(stage+1)) := by
      rw [← pow_mul, pow_succ]
    have hfactor : 2*errorFactor stage+3 = errorFactor (stage+1) := by
      simp only [errorFactor, pow_succ]
      ring
    rw [hpow, hfactor] at hsq
    have hnext := ih (stage+1) (Wasm.IEEE64.mul word word) (by omega) hsq.1 hsq.2
    simpa only [square, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext

theorem squared_polynomial_error (x : UInt64) (steps : Nat) (hs : steps ≤ 6)
    (hf : Finite x) (hl : -1 ≤ value x) (hu : value x ≤ 0) :
    Finite (square steps (polynomial x)) ∧
      |value (square steps (polynomial x))-Real.exp (value x)^(2^steps)| ≤
        4029*arithmeticEpsilon*Real.exp (value x)^(2^steps) := by
  have hp := polynomial_error x hf (abs_le.mpr ⟨hl, by linarith⟩)
  have hb := ExpSmall.exp_negative_unit_bounds (value x) hl hu
  have hsquare := square_error steps 0 (polynomial x) (Real.exp (value x)) (by simpa using hs)
    hb.1 hb.2 hp.1 (by
      simp only [errorFactor, pow_zero, pow_one]
      have hh := mul_le_mul_of_nonneg_right hb.1 (show 0 ≤ 60*arithmeticEpsilon by
        norm_num [arithmeticEpsilon])
      linarith only [hp.2, hh])
  simp only [Nat.zero_add] at hsquare
  refine ⟨hsquare.1, hsquare.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (errorFactor_bounds steps hs).2 F64ArithmeticBounds.epsilon_pos.le)
    (pow_nonneg (Real.exp_pos _).le _)

#print axioms squared_polynomial_error
end Project.ExpNeg
