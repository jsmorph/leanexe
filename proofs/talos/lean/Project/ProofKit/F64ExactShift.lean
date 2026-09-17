import Project.ProofKit.F64DyadicBounds

namespace Project.ProofKit.F64ExactShift
open CodeLib.IEEE64

/-- Shifting a significand with at most 53 bits introduces no rounding. -/
theorem rounded_shift (n shift : Nat) (hn : n < 2^53) :
    roundedMagnitude (n * 2^shift) = n * 2^shift := by
  by_cases hz : n = 0
  · subst n
    norm_num [roundedMagnitude]
  have hk : Nat.log2 n < 53 := (Nat.log2_lt hz).2 hn
  let padding := 52 - Nat.log2 n
  have hkpad : Nat.log2 n + padding = 52 := by dsimp [padding]; omega
  have hlo : 2^52 ≤ n * 2^padding := by
    calc
      2^52 = 2^(Nat.log2 n) * 2^padding := by rw [← pow_add, hkpad]
      _ ≤ n * 2^padding := Nat.mul_le_mul_right _ (Nat.log2_self_le hz)
  have hhi : n * 2^padding < 2^53 := by
    calc
      _ < 2^(Nat.log2 n + 1) * 2^padding :=
        Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (by positivity)
      _ = 2^53 := by rw [← pow_add, show Nat.log2 n + 1 + padding = 53 by omega]
  by_cases hs : shift < padding
  · have hsmall : n * 2^shift < 2^53 :=
      (Nat.mul_le_mul_left n (Nat.pow_le_pow_right (by omega) (by omega))).trans_lt hhi
    exact CodeLib.IEEE64.roundedMagnitude_eq_self hsmall.le
  · have hrepr := F64DyadicBounds.roundedMagnitude_shifted (n * 2^padding)
      (shift-padding) hlo hhi.le
    have heq : n * 2^padding * 2^(shift-padding) = n * 2^shift := by
      rw [Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega : padding ≤ shift)]
    simpa only [heq] using hrepr

#print axioms rounded_shift
end Project.ProofKit.F64ExactShift
