import Verified.Examples.ErfcTheorem
import LeanExe.ProofKit.F64Saturate

/-!
`Erfc.erfc` at the non-finite inputs: `erfc (+∞) = +0` (`erfc_pos_inf`), `erfc (-∞) = 2`
(`erfc_neg_inf`), and the canonical NaN for every NaN (`erfc_nan`), which the code computes as
`x + x`.  `ErfcBytes.erfc_bytes_accuracy` states that the compiled module returns the bits of
`Erfc.erfc x`, so the theorems hold for the module as well.
-/

namespace Verified.Examples.ErfcNonfinite
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- **`erfc (+∞) = +0`.** -/
theorem erfc_pos_inf : (Erfc.erfc (Float.ofBits 0x7FF0000000000000)).toBits = 0 := by
  unfold Erfc.erfc Erfc.erfcWith
  dsimp only
  rw [F64Bits.toBits_ofBits, ite_eq_right (by decide), ite_eq_left (by decide),
    ite_eq_left (by decide), ite_eq_left (by decide)]
  rfl

/-- **`erfc (-∞) = 2`.** -/
theorem erfc_neg_inf :
    (Erfc.erfc (Float.ofBits 0xFFF0000000000000)).toBits = 0x4000000000000000 := by
  unfold Erfc.erfc Erfc.erfcWith
  dsimp only
  rw [F64Bits.toBits_ofBits, ite_eq_left (by decide), ite_eq_left (by decide),
    ite_eq_left (by decide), ite_eq_left (by decide)]
  rfl

/-- **`erfc` at a NaN** is the canonical NaN. -/
theorem erfc_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Erfc.erfc x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hw := x.toBits.toNat_lt
  have hn : 0x7FF0000000000000 < x.toBits.toNat % 2 ^ 63 := by
    have h' := h
    simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at h'
    omega
  have hxx : (x + x).toBits = Wasm.IEEE64.canonicalNaN := by
    rw [F64Bits.toBits_add, F64Saturate.add_nan_left _ _ h]
  have ha := ErfcTheorem.and_mask x.toBits
  unfold Erfc.erfc Erfc.erfcWith
  dsimp only
  by_cases hs : 2 ^ 63 ≤ x.toBits.toNat
  · have c1 : x.toBits ≥ 0x8000000000000000 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le,
        show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl]
      exact hs
    have c2 : x.toBits ≥ 0xC017744F8F74E94B := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le,
        show (0xC017744F8F74E94B : UInt64).toNat = 0xC017744F8F74E94B from rfl]
      omega
    have c3 : x.toBits ≥ 0xFFF0000000000000 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le,
        show (0xFFF0000000000000 : UInt64).toNat = 0xFFF0000000000000 from rfl]
      omega
    have c4 : ¬ (x.toBits == 0xFFF0000000000000) = true := by
      rw [beq_iff_eq, ← UInt64.toNat_inj,
        show (0xFFF0000000000000 : UInt64).toNat = 0xFFF0000000000000 from rfl]
      omega
    rw [ite_eq_left c1, ite_eq_left c2, ite_eq_left c3, ite_eq_right c4]
    exact hxx
  · have c1 : ¬ x.toBits ≥ 0x8000000000000000 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le,
        show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl]
      exact hs
    have c2 : (x.toBits &&& 0x7FFFFFFFFFFFFFFF) ≥ 0x403B39DC41E48BFD := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, ha,
        show (0x403B39DC41E48BFD : UInt64).toNat = 0x403B39DC41E48BFD from rfl]
      omega
    have c3 : (x.toBits &&& 0x7FFFFFFFFFFFFFFF) ≥ 0x7FF0000000000000 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, ha,
        show (0x7FF0000000000000 : UInt64).toNat = 0x7FF0000000000000 from rfl]
      omega
    have c4 : ¬ ((x.toBits &&& 0x7FFFFFFFFFFFFFFF) == 0x7FF0000000000000) = true := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, ha,
        show (0x7FF0000000000000 : UInt64).toNat = 0x7FF0000000000000 from rfl]
      omega
    rw [ite_eq_right c1, ite_eq_left c2, ite_eq_left c3, ite_eq_right c4]
    exact hxx

#print axioms erfc_pos_inf
#print axioms erfc_neg_inf
#print axioms erfc_nan

end Verified.Examples.ErfcNonfinite
