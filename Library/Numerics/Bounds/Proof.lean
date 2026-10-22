import Library.Numerics.Bounds.Program
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64OutwardAccepted
import LeanExe.ProofKit.F64AdjacentSigned

namespace Library.Numerics.Bounds

open LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

theorem zero_toBits : (0 : Float).toBits = 0 := by decide +kernel

/-- A word whose exponent field is not all ones is not a NaN pattern. -/
theorem not_nan_of_exponent {w : UInt64} (h : ¬(w >>> 52) &&& 0x7FF = 0x7FF) :
    Wasm.IEEE64.isNaN w = false := by
  have hExp : Wasm.IEEE64.exponent w ≠ 0x7FF := by
    intro he
    apply h
    apply UInt64.toNat_inj.mp
    have hAnd : ((w >>> 52) &&& 0x7FF).toNat = w.toNat / 2 ^ 52 % 2 ^ 11 := by
      rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.and_two_pow_sub_one_eq_mod _ 11
    rw [hAnd]
    simpa [Wasm.IEEE64.exponent] using he
  simp [Wasm.IEEE64.isNaN, hExp]

/-- A word below the infinities in magnitude is not a NaN pattern. -/
theorem not_nan_of_finite {w : UInt64} (h : w &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000) :
    Wasm.IEEE64.isNaN w = false := by
  refine not_nan_of_exponent fun he => ?_
  have hAbs : (w &&& 0x7FFFFFFFFFFFFFFF).toNat = w.toNat % 2 ^ 63 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 63
  have hExp : ((w >>> 52) &&& 0x7FF).toNat = w.toNat / 2 ^ 52 % 2 ^ 11 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 11
  have h1 := congrArg UInt64.toNat he
  rw [hExp] at h1
  have h2 := UInt64.lt_iff_toNat_lt.mp h
  rw [hAbs] at h2
  simp only [UInt64.reduceToNat] at h1 h2
  omega

theorem toBits_ofBits_of_finite {w : UInt64}
    (h : w &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000) : (Float.ofBits w).toBits = w := by
  rw [F64Bits.toBits_ofBits, not_nan_of_finite h]
  rfl

/-- A checked value as a word-level checked value. -/
def checkedWord (c : Library.Numerics.Bounds.Checked) : LeanExe.ProofKit.F64Outward.Checked := ⟨c.status, c.value.toBits⟩

theorem endpoint_word (up : Bool) (r : Float) :
    checkedWord (Library.Numerics.Bounds.endpoint up r) = LeanExe.ProofKit.F64Outward.endpoint up r.toBits := by
  have hn : (if up then Library.Numerics.Bounds.nextUpBits r.toBits else Library.Numerics.Bounds.nextDownBits r.toBits) =
      LeanExe.ProofKit.F64Outward.neighbor up r.toBits := by
    cases up <;> simp [Library.Numerics.Bounds.nextUpBits, Library.Numerics.Bounds.nextDownBits, LeanExe.ProofKit.F64Outward.neighbor,
      LeanExe.ProofKit.F64Adjacent.nextUp, LeanExe.ProofKit.F64Adjacent.nextDown]
  unfold Library.Numerics.Bounds.endpoint LeanExe.ProofKit.F64Outward.endpoint
  dsimp only
  rw [hn]
  generalize LeanExe.ProofKit.F64Outward.neighbor up r.toBits = b
  by_cases h1 : r.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
    by_cases h2 : b &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
    simp [h1, h2, Library.Numerics.Bounds.finite, Library.Numerics.Bounds.absBits, LeanExe.ProofKit.F64Order.finiteBits,
      LeanExe.ProofKit.F64Order.absBits, checkedWord, Library.Numerics.Bounds.rejectedChecked,
      LeanExe.ProofKit.F64Outward.rejected, zero_toBits]
  exact toBits_ofBits_of_finite h2

open CodeLib.IEEE64 (value Finite)

theorem endpoint_rejected {up : Bool} {r : Float} (h : ¬(Library.Numerics.Bounds.endpoint up r).status = 0) :
    Library.Numerics.Bounds.endpoint up r = Library.Numerics.Bounds.rejectedChecked := by
  unfold Library.Numerics.Bounds.endpoint at h ⊢
  dsimp only at h ⊢
  generalize (if up then Library.Numerics.Bounds.nextUpBits r.toBits else Library.Numerics.Bounds.nextDownBits r.toBits) = w at h ⊢
  by_cases hc : (Library.Numerics.Bounds.finite r && decide (Library.Numerics.Bounds.absBits w < 0x7FF0000000000000)) = true
  · simp [hc] at h
  · simp only [hc, Bool.false_eq_true, ite_false]

theorem outAdd_word (up : Bool) (a b : Float) :
    checkedWord (Library.Numerics.Bounds.outAdd up a b) = LeanExe.ProofKit.F64Outward.add up a.toBits b.toBits := by
  unfold Library.Numerics.Bounds.outAdd LeanExe.ProofKit.F64Outward.add
  dsimp only
  rw [← F64Bits.toBits_add, ← endpoint_word]
  by_cases he : (Library.Numerics.Bounds.endpoint up (a + b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      simp [ha, hb, he, Library.Numerics.Bounds.finite, Library.Numerics.Bounds.absBits, LeanExe.ProofKit.F64Order.finiteBits,
        LeanExe.ProofKit.F64Order.absBits, checkedWord, Library.Numerics.Bounds.rejectedChecked,
        LeanExe.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, Library.Numerics.Bounds.rejectedChecked, LeanExe.ProofKit.F64Outward.rejected, zero_toBits]

theorem outAdd_accepted {up : Bool} {a b : Float} (h : (Library.Numerics.Bounds.outAdd up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧
      LeanExe.ProofKit.F64Outward.Sound up (checkedWord (Library.Numerics.Bounds.outAdd up a b)) (value a.toBits + value b.toBits) := by
  have := LeanExe.ProofKit.F64Outward.add_accepted up a.toBits b.toBits
    (by rw [← outAdd_word]; exact h)
  rwa [← outAdd_word] at this

theorem outSub_word (up : Bool) (a b : Float) :
    checkedWord (Library.Numerics.Bounds.outSub up a b) = LeanExe.ProofKit.F64Outward.sub up a.toBits b.toBits := by
  unfold Library.Numerics.Bounds.outSub LeanExe.ProofKit.F64Outward.sub
  dsimp only
  rw [← F64Bits.toBits_sub, ← endpoint_word]
  by_cases he : (Library.Numerics.Bounds.endpoint up (a - b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      simp [ha, hb, he, Library.Numerics.Bounds.finite, Library.Numerics.Bounds.absBits, LeanExe.ProofKit.F64Order.finiteBits,
        LeanExe.ProofKit.F64Order.absBits, checkedWord, Library.Numerics.Bounds.rejectedChecked,
        LeanExe.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, Library.Numerics.Bounds.rejectedChecked, LeanExe.ProofKit.F64Outward.rejected, zero_toBits]

theorem outSub_accepted {up : Bool} {a b : Float} (h : (Library.Numerics.Bounds.outSub up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧
      LeanExe.ProofKit.F64Outward.Sound up (checkedWord (Library.Numerics.Bounds.outSub up a b)) (value a.toBits - value b.toBits) := by
  have := LeanExe.ProofKit.F64Outward.sub_accepted up a.toBits b.toBits
    (by rw [← outSub_word]; exact h)
  rwa [← outSub_word] at this

theorem outMul_word (up : Bool) (a b : Float) :
    checkedWord (Library.Numerics.Bounds.outMul up a b) = LeanExe.ProofKit.F64Outward.mul up a.toBits b.toBits := by
  unfold Library.Numerics.Bounds.outMul LeanExe.ProofKit.F64Outward.mul
  dsimp only
  rw [← F64Bits.toBits_mul, ← endpoint_word]
  by_cases he : (Library.Numerics.Bounds.endpoint up (a * b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      simp [ha, hb, he, Library.Numerics.Bounds.finite, Library.Numerics.Bounds.absBits, LeanExe.ProofKit.F64Order.finiteBits,
        LeanExe.ProofKit.F64Order.absBits, checkedWord, Library.Numerics.Bounds.rejectedChecked,
        LeanExe.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, Library.Numerics.Bounds.rejectedChecked, LeanExe.ProofKit.F64Outward.rejected, zero_toBits]

theorem outMul_accepted {up : Bool} {a b : Float} (h : (Library.Numerics.Bounds.outMul up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧
      LeanExe.ProofKit.F64Outward.Sound up (checkedWord (Library.Numerics.Bounds.outMul up a b)) (value a.toBits * value b.toBits) := by
  have := LeanExe.ProofKit.F64Outward.mul_accepted up a.toBits b.toBits
    (by rw [← outMul_word]; exact h)
  rwa [← outMul_word] at this

theorem outDiv_word (up : Bool) (a b : Float) :
    checkedWord (Library.Numerics.Bounds.outDiv up a b) = LeanExe.ProofKit.F64Outward.div up a.toBits b.toBits := by
  unfold Library.Numerics.Bounds.outDiv LeanExe.ProofKit.F64Outward.div
  dsimp only
  rw [← F64Bits.toBits_div, ← endpoint_word]
  by_cases he : (Library.Numerics.Bounds.endpoint up (a / b)).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hb : b.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hz : 0 < b.toBits &&& 0x7FFFFFFFFFFFFFFF <;>
      simp [ha, hb, hz, he, Library.Numerics.Bounds.finite, Library.Numerics.Bounds.absBits, LeanExe.ProofKit.F64Order.finiteBits,
        LeanExe.ProofKit.F64Order.absBits, checkedWord, Library.Numerics.Bounds.rejectedChecked,
        LeanExe.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, Library.Numerics.Bounds.rejectedChecked, LeanExe.ProofKit.F64Outward.rejected, zero_toBits]

theorem outDiv_accepted {up : Bool} {a b : Float} (h : (Library.Numerics.Bounds.outDiv up a b).status = 0) :
    Finite a.toBits ∧ Finite b.toBits ∧ Wasm.IEEE64.scaledMagnitude b.toBits ≠ 0 ∧
      LeanExe.ProofKit.F64Outward.Sound up (checkedWord (Library.Numerics.Bounds.outDiv up a b))
        (value a.toBits / value b.toBits) := by
  have := LeanExe.ProofKit.F64Outward.div_accepted up a.toBits b.toBits
    (by rw [← outDiv_word]; exact h)
  rwa [← outDiv_word] at this

theorem outSqrt_word (up : Bool) (a : Float) :
    checkedWord (Library.Numerics.Bounds.outSqrt up a) = LeanExe.ProofKit.F64Outward.sqrt up a.toBits := by
  unfold Library.Numerics.Bounds.outSqrt LeanExe.ProofKit.F64Outward.sqrt
  dsimp only
  rw [← F64Bits.toBits_sqrt, ← endpoint_word]
  by_cases he : (Library.Numerics.Bounds.endpoint up a.sqrt).status = 0
  · by_cases ha : a.toBits &&& 0x7FFFFFFFFFFFFFFF < 0x7FF0000000000000 <;>
      by_cases hs : a.toBits ≤ 0x8000000000000000 <;>
      simp [ha, hs, he, Library.Numerics.Bounds.finite, Library.Numerics.Bounds.absBits, LeanExe.ProofKit.F64Order.finiteBits,
        LeanExe.ProofKit.F64Order.absBits, checkedWord, Library.Numerics.Bounds.rejectedChecked,
        LeanExe.ProofKit.F64Outward.rejected, zero_toBits]
  · rw [endpoint_rejected he]
    simp [checkedWord, Library.Numerics.Bounds.rejectedChecked, LeanExe.ProofKit.F64Outward.rejected, zero_toBits]

theorem outSqrt_accepted {up : Bool} {a : Float} (h : (Library.Numerics.Bounds.outSqrt up a).status = 0) :
    Finite a.toBits ∧ 0 ≤ value a.toBits ∧
      LeanExe.ProofKit.F64Outward.Sound up (checkedWord (Library.Numerics.Bounds.outSqrt up a))
        (Real.sqrt (value a.toBits)) := by
  have := LeanExe.ProofKit.F64Outward.sqrt_accepted up a.toBits (by rw [← outSqrt_word]; exact h)
  rwa [← outSqrt_word] at this

end Library.Numerics.Bounds
