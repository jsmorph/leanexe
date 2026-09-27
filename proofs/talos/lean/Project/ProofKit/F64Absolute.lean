import Project.ProofKit.F64Normalize

namespace Project.ProofKit.F64Order
open CodeLib.IEEE64

theorem absBits_idempotent (a : UInt64) : absBits (absBits a) = absBits a := by
  apply UInt64.toNat_inj.mp
  rw [absBits_toNat, absBits_toNat, Nat.mod_mod]

theorem absBits_sign (a : UInt64) : Wasm.IEEE64.sign (absBits a) = false := by
  simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le, absBits_toNat]
  exact Nat.mod_lt _ (by decide)

theorem absBits_finite (a : UInt64) (ha : Finite a) : Finite (absBits a) := by
  apply (finiteBits_iff _).mp
  simpa only [finiteBits, absBits_idempotent] using (finiteBits_iff a).mpr ha

theorem absBits_value (a : UInt64) : value (absBits a) = |value a| := by
  have hm : Wasm.IEEE64.scaledMagnitude (absBits a) = Wasm.IEEE64.scaledMagnitude a := by
    rw [scaledMagnitude_abs, absBits_idempotent, ← scaledMagnitude_abs]
  rw [F64Normalize.abs_value_scaledMagnitude]
  simp only [value, Wasm.IEEE64.scaledValue, absBits_sign, Bool.false_eq_true, ite_false,
    Int.cast_natCast, hm]

def negativeAbsBits (a : UInt64) : UInt64 := absBits a + 0x8000000000000000

theorem negativeAbsBits_toNat (a : UInt64) :
    (negativeAbsBits a).toNat = a.toNat % 2^63 + 2^63 := by
  have h := Nat.mod_lt a.toNat (by norm_num : 0 < 2^63)
  simp only [negativeAbsBits, UInt64.toNat_add, absBits_toNat, UInt64.toNat_ofNat]
  norm_num
  omega

theorem absBits_negativeAbsBits (a : UInt64) : absBits (negativeAbsBits a) = absBits a := by
  apply UInt64.toNat_inj.mp
  rw [absBits_toNat, negativeAbsBits_toNat, absBits_toNat]
  simp

theorem negativeAbsBits_sign (a : UInt64) : Wasm.IEEE64.sign (negativeAbsBits a) = true := by
  simp only [Wasm.IEEE64.sign, decide_eq_true_eq, negativeAbsBits_toNat]
  omega

theorem negativeAbsBits_finite (a : UInt64) (ha : Finite a) : Finite (negativeAbsBits a) := by
  apply (finiteBits_iff _).mp
  simpa only [finiteBits, absBits_negativeAbsBits] using (finiteBits_iff a).mpr ha

theorem negativeAbsBits_value (a : UInt64) : value (negativeAbsBits a) = -|value a| := by
  have hm : Wasm.IEEE64.scaledMagnitude (negativeAbsBits a) = Wasm.IEEE64.scaledMagnitude a := by
    rw [scaledMagnitude_abs, absBits_negativeAbsBits, ← scaledMagnitude_abs]
  rw [F64Normalize.abs_value_scaledMagnitude]
  simp only [value, Wasm.IEEE64.scaledValue, negativeAbsBits_sign, ite_true,
    Int.cast_neg, Int.cast_natCast, hm, neg_div]

#print axioms absBits_finite
#print axioms absBits_value
#print axioms negativeAbsBits_value
end Project.ProofKit.F64Order
