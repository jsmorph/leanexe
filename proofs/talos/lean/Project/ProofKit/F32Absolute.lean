import Project.ProofKit.F32Order

namespace Project.ProofKit.F32Order
open CodeLib.IEEE32

theorem abs_value_scaledMagnitude (a : UInt32) :
    |value a| = (Wasm.IEEE32.scaledMagnitude a : ℝ) / 2 ^ 149 := by
  simp only [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 149), Wasm.IEEE32.scaledValue]
  split <;> simp


theorem absBits_idempotent (a : UInt32) : absBits (absBits a) = absBits a := by
  apply UInt32.toNat_inj.mp
  rw [absBits_toNat, absBits_toNat, Nat.mod_mod]

theorem absBits_sign (a : UInt32) : Wasm.IEEE32.sign (absBits a) = false := by
  simp only [Wasm.IEEE32.sign, decide_eq_false_iff_not, not_le, absBits_toNat]
  exact Nat.mod_lt _ (by decide)

theorem absBits_finite (a : UInt32) (ha : Finite a) : Finite (absBits a) := by
  apply (finiteBits_iff _).mp
  simpa only [finiteBits, absBits_idempotent] using (finiteBits_iff a).mpr ha

theorem absBits_value (a : UInt32) : value (absBits a) = |value a| := by
  have hm : Wasm.IEEE32.scaledMagnitude (absBits a) = Wasm.IEEE32.scaledMagnitude a := by
    rw [scaledMagnitude_abs, absBits_idempotent, ← scaledMagnitude_abs]
  rw [abs_value_scaledMagnitude]
  simp only [value, Wasm.IEEE32.scaledValue, absBits_sign, Bool.false_eq_true, ite_false,
    Int.cast_natCast, hm]

def negativeAbsBits (a : UInt32) : UInt32 := absBits a + 0x80000000

theorem negativeAbsBits_toNat (a : UInt32) :
    (negativeAbsBits a).toNat = a.toNat % 2^31 + 2^31 := by
  have h := Nat.mod_lt a.toNat (by norm_num : 0 < 2^31)
  simp only [negativeAbsBits, UInt32.toNat_add, absBits_toNat, UInt32.toNat_ofNat]
  norm_num
  omega

theorem absBits_negativeAbsBits (a : UInt32) : absBits (negativeAbsBits a) = absBits a := by
  apply UInt32.toNat_inj.mp
  rw [absBits_toNat, negativeAbsBits_toNat, absBits_toNat]
  simp

theorem negativeAbsBits_sign (a : UInt32) : Wasm.IEEE32.sign (negativeAbsBits a) = true := by
  simp only [Wasm.IEEE32.sign, decide_eq_true_eq, negativeAbsBits_toNat]
  omega

theorem negativeAbsBits_finite (a : UInt32) (ha : Finite a) : Finite (negativeAbsBits a) := by
  apply (finiteBits_iff _).mp
  simpa only [finiteBits, absBits_negativeAbsBits] using (finiteBits_iff a).mpr ha

theorem negativeAbsBits_value (a : UInt32) : value (negativeAbsBits a) = -|value a| := by
  have hm : Wasm.IEEE32.scaledMagnitude (negativeAbsBits a) = Wasm.IEEE32.scaledMagnitude a := by
    rw [scaledMagnitude_abs, absBits_negativeAbsBits, ← scaledMagnitude_abs]
  rw [abs_value_scaledMagnitude]
  simp only [value, Wasm.IEEE32.scaledValue, negativeAbsBits_sign, ite_true,
    Int.cast_neg, Int.cast_natCast, hm, neg_div]

theorem negativeAbsBits_eq_or (a : UInt32) : negativeAbsBits a = a ||| 0x80000000 := by
  have hMasked : (absBits a ||| 0x80000000) = (a ||| 0x80000000) := by
    apply UInt32.toBitVec_inj.mp
    simp only [absBits, UInt32.toBitVec_or, UInt32.toBitVec_and]
    apply BitVec.eq_of_getLsbD_eq
    intro bit hBit
    interval_cases bit <;> simp
  rw [← hMasked]
  apply UInt32.toNat_inj.mp
  rw [negativeAbsBits_toNat, UInt32.toNat_or, absBits_toNat]
  change a.toNat % 2 ^ 31 + 2 ^ 31 = a.toNat % 2 ^ 31 ||| 2 ^ 31
  exact (Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt _ (by decide))).symm

theorem value_nonnegative (a : UInt32) (h : a < 0x80000000) : 0 ≤ value a := by
  have hs : Wasm.IEEE32.sign a = false := by
    change decide (2 ^ 31 ≤ a.toNat) = false
    change a.toNat < (0x80000000 : UInt32).toNat at h
    simp only [decide_eq_false_iff_not]
    exact Nat.not_le_of_gt h
  simp only [value, Wasm.IEEE32.scaledValue, hs, Bool.false_eq_true, ite_false]
  positivity

theorem value_nonpositive (a : UInt32) (h : ¬a < 0x80000000) : value a ≤ 0 := by
  have hs : Wasm.IEEE32.sign a = true := by
    change decide (2 ^ 31 ≤ a.toNat) = true
    change ¬a.toNat < (0x80000000 : UInt32).toNat at h
    simp only [decide_eq_true_eq]
    exact Nat.le_of_not_gt h
  simp only [value, Wasm.IEEE32.scaledValue, hs, ite_true]
  exact div_nonpos_of_nonpos_of_nonneg (by simp) (by positivity)

#print axioms absBits_finite
#print axioms absBits_value
#print axioms negativeAbsBits_value
#print axioms negativeAbsBits_eq_or
end Project.ProofKit.F32Order
