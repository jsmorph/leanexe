import Project.ProofKit.F64ExactArithmetic
import Project.ProofKit.F64OrderComplete

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

def shiftInteger (word : UInt64) : Int := (word.toNat : Int) - 0x4338000000000000

theorem shift_word (word : UInt64)
    (hl : 0x4330000000000000 ≤ word) (hu : word < 0x4340000000000000) :
    Finite word ∧ Wasm.IEEE64.sign word = false ∧
    Wasm.IEEE64.scaledValue word =
      (shiftInteger word + 6755399441055744) * (2 : Int)^1074 := by
  have hl' : 4841369599423283200 ≤ word.toNat := UInt64.le_iff_toNat_le.mp hl
  have hu' : word.toNat < 4845873199050653696 := UInt64.lt_iff_toNat_lt.mp hu
  have he : Wasm.IEEE64.exponent word = 1075 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have hs : Wasm.IEEE64.sign word = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
    omega
  have hn : 4503599627370496 + word.toNat % 4503599627370496 =
      word.toNat - 4836865999795912704 := by omega
  refine ⟨?_, hs, ?_⟩
  · change (Wasm.IEEE64.exponent word != 2047) = true
    rw [he]
    decide
  · simp only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Wasm.IEEE64.scaledMagnitude, he, Wasm.IEEE64.fraction, beq_iff_eq,
      show (1075 : Nat) ≠ 0 by decide, ite_false]
    change (((4503599627370496 + word.toNat % 4503599627370496) * 2^1074 : Nat) : Int) = _
    rw [hn, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    congr 1
    dsimp [shiftInteger]
    omega

theorem shiftInteger_bound (word : UInt64)
    (hl : 0x4330000000000000 ≤ word) (hu : word < 0x4340000000000000) :
    (shiftInteger word).natAbs < 2^52 := by
  have hl' : 4841369599423283200 ≤ word.toNat := UInt64.le_iff_toNat_le.mp hl
  have hu' : word.toNat < 4845873199050653696 := UInt64.lt_iff_toNat_lt.mp hu
  dsimp [shiftInteger]
  omega

theorem shift_sub_exact (word : UInt64)
    (hl : 0x4330000000000000 ≤ word) (hu : word < 0x4340000000000000) :
    Finite (Wasm.IEEE64.sub word 0x4338000000000000) ∧
    value (Wasm.IEEE64.sub word 0x4338000000000000) = (shiftInteger word : ℝ) := by
  have hw := shift_word word hl hu
  have hn := shiftInteger_bound word hl hu
  have hc : Wasm.IEEE64.scaledValue 0x4338000000000000 =
      (6755399441055744 : Int) * 2^1074 := by rfl
  have hg := negate_spec 0x4338000000000000 (by rfl)
  have hz : Wasm.IEEE64.scaledValue word +
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate 0x4338000000000000) =
      shiftInteger word * (2 : Int)^1074 := by
    rw [hw.2.2, hg.2, hc]
    ring
  have hm : (shiftInteger word).natAbs * 2^1074 < 2^2097 := by
    calc
      _ < 2^52 * 2^1074 := Nat.mul_lt_mul_of_pos_right hn (by positivity)
      _ < _ := by norm_num
  have h := F64ExactArithmetic.add_exact_scaled word
    (Wasm.IEEE64.negate 0x4338000000000000) hw.1 hg.1
    (shiftInteger word).natAbs 1074 (by omega)
    (by rw [hz, Int.natAbs_mul]; rfl) hm
  refine ⟨h.1, ?_⟩
  rw [hz] at h
  change (Wasm.IEEE64.scaledValue (Wasm.IEEE64.add word
    (Wasm.IEEE64.negate 0x4338000000000000)) : ℝ) / 2^1074 = _
  rw [h.2, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp

#print axioms shift_word
#print axioms shift_sub_exact
end Project.ExpArm
