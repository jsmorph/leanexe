import Verified.Examples.Log1pTheorem
import Verified.Examples.AtanTheoremReduce

/-!
The exceptional inputs of `Log1p.log1p` as words: `-1` gives `-∞`, `+∞` gives `+∞`, `±0` give
`±0`, and an `x` below `-1`, `-∞`, and NaN give the canonical NaN.  An `x` below `-1` takes the
first branch, where `x - x = +0` and `0/0` is NaN.
-/

namespace Verified.Examples.Log1pTheoremSpecial
open CodeLib.IEEE64 LeanExe.ProofKit Log1pTheoremBranches Log1pTheorem

set_option exponentiation.threshold 4096

theorem float_of_bits (x : Float) (w : UInt64) (h : x.toBits = w) : x = Float.ofBits w := by
  rw [← h, F64Bits.ofBits_toBits]

theorem log1p_neg_one (x : Float) (h : x.toBits = 0xBFF0000000000000) :
    (Log1p.log1p x).toBits = 0xFFF0000000000000 := by
  rw [log1p_b1_eq x (by simp only [hxOf, axOf, h]; decide)]
  have he : (x == -1.0) = true := by
    rw [F64Bits.beq_eq, h, AtanTheoremReduce.neg_one_bits]
    decide
  rw [if_pos he, F64Bits.toBits_div, F64Bits.toBits_neg, F64Bits.toBits_ofBits,
    show (0.0 : Float).toBits = 0 from rfl]
  decide +kernel

theorem log1p_pos_inf (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Log1p.log1p x).toBits = 0x7FF0000000000000 := by
  rw [log1p_b4_eq x (by simp only [hxOf, axOf, h]; decide) (by simp only [hxOf, axOf, h]; decide)
    (by simp only [hxOf, axOf, h]; decide) (by simp only [hxOf, axOf, h]; decide),
    F64Bits.toBits_add, h]
  decide +kernel

theorem log1p_zero (x : Float) (h : x.toBits = 0) : (Log1p.log1p x).toBits = 0 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value x.toBits = 0 := by rw [h]; exact F64Magnitude.value_zero
  rw [log1p_tiny_eq x (by simp only [hxOf, h]; decide) (by simp only [axOf, hxOf, h]; decide),
    two54_sum x hx (by rw [hv, abs_zero]; norm_num)]
  rw [show (true && decide (axOf x < 0x3c900000)) = true by
    simp only [axOf, hxOf, h]; decide, if_pos rfl, h]

theorem log1p_neg_zero (x : Float) (h : x.toBits = 0x8000000000000000) :
    (Log1p.log1p x).toBits = 0x8000000000000000 := by
  have hx : Finite x.toBits := by rw [h]; unfold CodeLib.IEEE64.Finite; decide
  have hv : value x.toBits = 0 := by
    rw [h, show value 0x8000000000000000 = 0 by
      rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x8000000000000000 = 0 by
        decide +kernel]; norm_num]
  rw [log1p_tiny_eq x (by simp only [hxOf, h]; decide) (by simp only [axOf, hxOf, h]; decide),
    two54_sum x hx (by rw [hv, abs_zero]; norm_num)]
  rw [show (true && decide (axOf x < 0x3c900000)) = true by
    simp only [axOf, hxOf, h]; decide, if_pos rfl, h]

/-- `x - x` is `+0` for a finite `x`. -/
theorem sub_self_bits (w : UInt64) (hw : Finite w) : Wasm.IEEE64.sub w w = 0 := by
  have hn := F64Magnitude.negate_value w hw
  have hs : Wasm.IEEE64.scaledValue w + Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate w) = 0 := by
    have h1 : (Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate w) : ℝ) =
        -(Wasm.IEEE64.scaledValue w : ℝ) := by
      have := hn.2
      simp only [value] at this
      field_simp at this
      linarith
    have h2 : ((Wasm.IEEE64.scaledValue w + Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate w) : ℤ) :
        ℝ) = 0 := by push_cast; linarith
    exact_mod_cast h2
  have hsn : (Wasm.IEEE64.sign w && Wasm.IEEE64.sign (Wasm.IEEE64.negate w)) = false := by
    have := (F64Sign.fields_negate w).2.2
    rw [this]
    cases Wasm.IEEE64.sign w <;> rfl
  simp only [Wasm.IEEE64.sub, Wasm.IEEE64.add, not_nan_of_finite hw, not_nan_of_finite hn.1,
    not_infinite_of_finite hw, not_infinite_of_finite hn.1, Bool.or_false, Bool.false_eq_true,
    ite_false, hs, beq_self_eq_true, ite_true, hsn]

theorem log1p_below (x : Float) (hx : Finite x.toBits) (h : value x.toBits < -1) :
    (Log1p.log1p x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hN := x.toBits.toNat_lt
  obtain ⟨hsn, hsp⟩ := sign_value x hx
  have hneg : 2 ^ 63 ≤ x.toBits.toNat := by
    by_contra hc
    have := hsp (by omega)
    linarith
  have T1 := ax_lt x 0x3ff00000 (by norm_num) 1 (by decide +kernel)
  rw [ax_toNat] at T1
  push_cast at T1
  have c1 : ¬ x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x3ff00000 := by
    intro hc
    have := T1.mp hc
    rw [abs_lt] at this
    linarith [this.1]
  rw [log1p_b1_eq x (by bits_omega)]
  have he : (x == -1.0) = false := by
    cases hb : (x == -1.0)
    · rfl
    · have := (F64UpperWord.float_beq_iff x (-1.0) hx (by
        rw [AtanTheoremReduce.neg_one_bits]; unfold CodeLib.IEEE64.Finite; decide)).mp hb
      rw [AtanTheoremReduce.neg_one_bits, show value 0xBFF0000000000000 = -1 by
        rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0xBFF0000000000000 = -1 by
          decide +kernel]; norm_num] at this
      linarith
  rw [if_neg (by rw [he]; decide), F64Bits.toBits_div, F64Bits.toBits_sub, sub_self_bits _ hx]
  decide +kernel

theorem log1p_neg_inf (x : Float) (h : x.toBits = 0xFFF0000000000000) :
    (Log1p.log1p x).toBits = Wasm.IEEE64.canonicalNaN := by
  rw [log1p_b1_eq x (by simp only [hxOf, axOf, h]; decide)]
  have he : (x == -1.0) = false := by
    rw [F64Bits.beq_eq, h, AtanTheoremReduce.neg_one_bits]
    decide
  rw [if_neg (by rw [he]; decide), F64Bits.toBits_div, F64Bits.toBits_sub, h]
  decide +kernel

theorem log1p_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Log1p.log1p x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hN := x.toBits.toNat_lt
  have hb : x.toBits.toNat % 2 ^ 63 / 2 ^ 52 = 2047 ∧ x.toBits.toNat % 2 ^ 52 ≠ 0 := by
    simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at h
    omega
  have hadd : ∀ w : UInt64, Wasm.IEEE64.isNaN w = true →
      Wasm.IEEE64.add w w = Wasm.IEEE64.canonicalNaN := by
    intro w hw
    simp only [Wasm.IEEE64.add, hw, Bool.true_or, ite_true]
  rcases Nat.lt_or_ge x.toBits.toNat (2 ^ 63) with hpos | hneg
  · rw [log1p_b4_eq x (by bits_omega) (by bits_omega) (by bits_omega) (by bits_omega),
      F64Bits.toBits_add, hadd _ h]
  · rw [log1p_b1_eq x (by bits_omega)]
    have he : (x == -1.0) = false := by
      rw [F64Bits.beq_eq, AtanTheoremReduce.neg_one_bits]
      simp only [Wasm.IEEE64.eq, h, Bool.true_or, ite_true]
    have hs : Wasm.IEEE64.sub x.toBits x.toBits = Wasm.IEEE64.canonicalNaN := by
      simp only [Wasm.IEEE64.sub, Wasm.IEEE64.add, h, Bool.true_or, ite_true]
    rw [if_neg (by rw [he]; decide), F64Bits.toBits_div, F64Bits.toBits_sub, hs]
    decide +kernel

#print axioms log1p_neg_one
#print axioms log1p_pos_inf
#print axioms log1p_zero
#print axioms log1p_neg_zero
#print axioms log1p_below
#print axioms log1p_neg_inf
#print axioms log1p_nan

end Verified.Examples.Log1pTheoremSpecial
