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

#print axioms absBits_finite
#print axioms absBits_value
end Project.ProofKit.F64Order
