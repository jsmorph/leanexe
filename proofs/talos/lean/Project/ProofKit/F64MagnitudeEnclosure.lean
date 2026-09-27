import Project.ProofKit.F64MagnitudeGaps
import Project.ProofKit.F64RoundingScale

namespace Project.ProofKit.F64Adjacent
open Project.ProofKit.F64Order
set_option exponentiation.threshold 4096

theorem half_step_le_gap (n shift : Nat)
    (hn : shift = 0 ∨ 2^52*2^shift ≤ unsignedScaled n) :
    (2:ℝ)^shift/2 ≤ (2:ℝ)^(n/2^52-1) := by
  rcases hn with hz | hn
  · rw [hz, pow_zero]
    have hp : (1:ℝ) ≤ (2:ℝ)^(n/2^52-1) := one_le_pow₀ (by norm_num)
    linarith
  · have hg : (2:ℝ)^shift ≤ (2:ℝ)^(n/2^52-1) := by
      exact_mod_cast gap_lower_of_magnitude n shift hn
    have hp : (0:ℝ) ≤ (2:ℝ)^shift := by positivity
    linarith

theorem half_step_le_predecessor_gap (n shift : Nat) (hp : 0 < n)
    (hn : shift = 0 ∨ 2^52*2^shift ≤ unsignedScaled n) :
    (2:ℝ)^shift/2 ≤ (2:ℝ)^((n-1)/2^52-1) := by
  by_cases hz : shift = 0
  · exact half_step_le_gap (n-1) shift (Or.inl hz)
  · have hn := hn.resolve_left hz
    have hl : 2^52*2^(shift-1) < unsignedScaled ((n-1)+1) := by
      rw [Nat.sub_add_cancel hp]
      exact (Nat.mul_lt_mul_of_pos_left
        (Nat.pow_lt_pow_right (by omega) (by omega)) (by positivity)).trans_le hn
    have hg : (2:ℝ)^(shift-1) ≤ (2:ℝ)^((n-1)/2^52-1) := by
      exact_mod_cast predecessor_gap_lower (n-1) (shift-1) hl
    have he : (2:ℝ)^shift/2 = (2:ℝ)^(shift-1) := by
      conv_lhs => rw [show shift = (shift-1)+1 by omega, pow_succ]
      ring
    rw [he]
    exact hg

theorem magnitude_enclosure (n shift : Nat) (x : ℝ) (hx : 0 ≤ x)
    (hn : shift = 0 ∨ 2^52*2^shift ≤ unsignedScaled n)
    (he : |(unsignedScaled n : ℝ)-x| ≤ (2:ℝ)^shift/2) :
    (if n = 0 then -(1:ℝ) else (unsignedScaled (n-1) : ℝ)) ≤ x ∧
      x ≤ (unsignedScaled (n+1) : ℝ) := by
  have he := abs_le.mp he
  constructor
  · by_cases hz : n = 0
    · rw [ite_eq_left hz]
      linarith
    · rw [ite_eq_right hz]
      have hg := half_step_le_predecessor_gap n shift (by omega) hn
      have hs := unsignedScaled_succ (n-1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hs
      have hsReal : (unsignedScaled n : ℝ) =
          (unsignedScaled (n-1) : ℝ)+(2:ℝ)^((n-1)/2^52-1) := by exact_mod_cast hs
      linarith [he.2]
  · have hg := half_step_le_gap n shift hn
    have hsReal : (unsignedScaled (n+1) : ℝ) =
        (unsignedScaled n : ℝ)+(2:ℝ)^(n/2^52-1) := by
      exact_mod_cast unsignedScaled_succ n
    linarith [he.1]

#print axioms half_step_le_predecessor_gap
#print axioms magnitude_enclosure
end Project.ProofKit.F64Adjacent
