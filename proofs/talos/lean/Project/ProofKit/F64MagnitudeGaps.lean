import Project.ProofKit.F64AdjacentSigned

namespace Project.ProofKit.F64Adjacent
open Project.ProofKit.F64Order
set_option exponentiation.threshold 4096

theorem unsignedScaled_lt (n : Nat) :
    unsignedScaled n < 2^53*2^(n/2^52-1) := by
  have hf : n%2^52 < 2^52 := Nat.mod_lt _ (by positivity)
  unfold unsignedScaled
  split
  · rename_i he
    simp only [he, Nat.zero_sub, pow_zero, Nat.mul_one]
    omega
  · exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)

theorem unsignedScaled_succ_le (n : Nat) :
    unsignedScaled (n+1) ≤ 2^53*2^(n/2^52-1) := by
  rw [unsignedScaled_succ]
  have hf : n%2^52+1 ≤ 2^52 := by omega
  unfold unsignedScaled
  split
  · rename_i he
    simp only [he, Nat.zero_sub, pow_zero, Nat.mul_one]
    omega
  · calc
      (2^52+n%2^52)*2^(n/2^52-1)+2^(n/2^52-1) =
          (2^52+(n%2^52+1))*2^(n/2^52-1) := by ring
      _ ≤ 2^53*2^(n/2^52-1) := Nat.mul_le_mul_right _ (by omega)

theorem gap_lower_of_magnitude (n shift : Nat)
    (h : 2^52*2^shift ≤ unsignedScaled n) :
    2^shift ≤ 2^(n/2^52-1) := by
  by_cases he : shift ≤ n/2^52-1
  · exact Nat.pow_le_pow_right (by omega) he
  · have hp : 2^53*2^(n/2^52-1) ≤ 2^52*2^shift := by
      calc
        2^53*2^(n/2^52-1) = 2^52*2^((n/2^52-1)+1) := by
          rw [pow_succ]
          ring
        _ ≤ 2^52*2^shift := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by omega) (by omega))
    exact False.elim ((not_lt_of_ge h) ((unsignedScaled_lt n).trans_le hp))

theorem predecessor_gap_lower (n shift : Nat)
    (h : 2^52*2^shift < unsignedScaled (n+1)) :
    2^shift ≤ 2^(n/2^52-1) := by
  by_cases he : shift ≤ n/2^52-1
  · exact Nat.pow_le_pow_right (by omega) he
  · have hp : 2^53*2^(n/2^52-1) ≤ 2^52*2^shift := by
      calc
        2^53*2^(n/2^52-1) = 2^52*2^((n/2^52-1)+1) := by
          rw [pow_succ]
          ring
        _ ≤ 2^52*2^shift := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by omega) (by omega))
    exact False.elim ((not_lt_of_ge ((unsignedScaled_succ_le n).trans hp)) h)

#print axioms gap_lower_of_magnitude
#print axioms predecessor_gap_lower
end Project.ProofKit.F64Adjacent
