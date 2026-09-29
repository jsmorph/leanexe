import Project.ProofKit.F32Source

namespace Project.ProofKit.F32Rounding
open Float.Model.UnpackedFloat

theorem shift_zero (em : ExtendedMantissa) : em >>> (0 : Nat) = em := rfl

theorem shift_succ (em : ExtendedMantissa) (n : Nat) :
    em >>> (n + 1) = (em >>> n).shiftRightOne := by
  change Nat.repeat _ (n + 1) em = _
  rfl

theorem shift_mantissa (em : ExtendedMantissa) (n : Nat) :
    (em >>> n).mantissa = em.mantissa / 2 ^ n := by
  induction n with
  | zero => simp [shift_zero]
  | succ n ih =>
    rw [shift_succ]
    simp only [ExtendedMantissa.shiftRightOne, ih, Nat.div_div_eq_div_mul, pow_succ]

theorem shift_roundBit (em : ExtendedMantissa) (n : Nat) :
    (em >>> (n + 1)).roundBit = (em.mantissa / 2 ^ n % 2 != 0) := by
  rw [shift_succ]
  simp only [ExtendedMantissa.shiftRightOne, shift_mantissa]

theorem remainder_nonzero (m n : Nat) :
    (m % 2 ^ (n + 1) != 0) =
      ((m / 2 ^ n % 2 != 0) || (m % 2 ^ n != 0)) := by
  rw [pow_succ, Nat.mod_mul]
  apply Bool.eq_iff_iff.mpr
  simp
  tauto

theorem shift_stickyBit (em : ExtendedMantissa) (n : Nat) :
    (em >>> (n + 1)).stickyBit =
      (em.roundBit || em.stickyBit || (em.mantissa % 2 ^ n != 0)) := by
  induction n with
  | zero => simp [shift_succ, shift_zero, ExtendedMantissa.shiftRightOne, Nat.mod_one]
  | succ n ih =>
    rw [shift_succ]
    simp only [ExtendedMantissa.shiftRightOne, shift_roundBit, ih, remainder_nonzero]
    cases em.roundBit <;> cases em.stickyBit <;>
      cases (em.mantissa / 2 ^ n % 2 != 0) <;>
      cases (em.mantissa % 2 ^ n != 0) <;> rfl

theorem roundedMantissa_eq (em : ExtendedMantissa) :
    em.roundedMantissa = if em.roundBit then
      if em.stickyBit then em.mantissa + 1 else em.mantissa + em.mantissa % 2
      else em.mantissa := by
  obtain ⟨m, r, s⟩ := em
  cases r <;> cases s <;> rfl

theorem round_exact_shift (m n : Nat) :
    ((ExtendedMantissa.ofMantissaAndAccuracy m .exact) >>> (n + 1)).roundedMantissa =
      Wasm.IEEE32.roundShift m (n + 1) := by
  rw [roundedMantissa_eq, shift_mantissa, shift_roundBit, shift_stickyBit]
  simp only [ExtendedMantissa.ofMantissaAndAccuracy, Bool.false_or]
  have hp : 0 < 2 ^ n := pow_pos (by decide) _
  have hr := Nat.mod_lt m hp
  have hb := Nat.mod_lt (m / 2 ^ n) (by decide : 0 < 2)
  have hq := Nat.mod_lt (m / 2 ^ (n + 1)) (by decide : 0 < 2)
  have hm : m % 2 ^ (n + 1) = m % 2 ^ n + 2 ^ n * (m / 2 ^ n % 2) := by
    rw [pow_succ, Nat.mod_mul]
  have hh : 2 ^ (n + 1) / 2 = 2 ^ n := by simp [pow_succ]
  unfold Wasm.IEEE32.roundShift
  dsimp only
  rw [hh, hm]
  by_cases hb0 : m / 2 ^ n % 2 = 0
  · simp [hb0, hr]
  · have hb1 : m / 2 ^ n % 2 = 1 := by omega
    by_cases hr0 : m % 2 ^ n = 0
    · simp [hb1, hr0]
      split <;> simp_all
    · have hlt : 2 ^ n < m % 2 ^ n + 2 ^ n := by omega
      simp [hb1, hr0, hlt, Nat.not_lt.mpr (Nat.le_of_lt hlt)]

#print axioms round_exact_shift

end Project.ProofKit.F32Rounding
