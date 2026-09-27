import Project.ExpArm.ShiftWords
import Project.ProofKit.F64AddUlp

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem shift_constants :
    value 0x4338000000000000 = 6755399441055744 ∧
    value 0x4330000000000000 = 4503599627370496 ∧
    value 0x4340000000000000 = 9007199254740992 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem shift_rounding (z : UInt64) (hf : Finite z) (hz : |value z| ≤ 190000) :
    let word := Wasm.IEEE64.add z 0x4338000000000000
    0x4330000000000000 ≤ word ∧ word < 0x4340000000000000 ∧
    Finite (Wasm.IEEE64.sub word 0x4338000000000000) ∧
    value (Wasm.IEEE64.sub word 0x4338000000000000) = (shiftInteger word : ℝ) ∧
    |(shiftInteger word : ℝ) - value z| ≤ 1/2 := by
  dsimp only
  let word := Wasm.IEEE64.add z 0x4338000000000000
  have hsum : |value z + value 0x4338000000000000| < (2 : ℝ)^53 := by
    rw [shift_constants.1]
    rcases abs_le.mp hz with ⟨hl, hu⟩
    rw [abs_lt]
    norm_num
    constructor <;> linarith
  have ha := F64AddUlp.add_real_binade z 0x4338000000000000 hf (by rfl) 53 (by decide) hsum
  have he : |value word - (value z + 6755399441055744)| ≤ 1/2 := by
    simpa only [shift_constants.1, show (2 : ℝ)^53/2^54 = 1/2 by norm_num] using ha.2
  have hv : 4503599627370496 < value word ∧ value word < 9007199254740992 := by
    rcases abs_le.mp hz with ⟨hzl, hzu⟩
    rcases abs_le.mp he with ⟨hel, heu⟩
    constructor <;> linarith
  have hp := F64Order.positiveBits_of_finite_value_pos word ha.1 (by linarith [hv.1])
  have hl : 0x4330000000000000 ≤ word := by
    have hlt := (F64Order.positive_word_lt_iff 0x4330000000000000 word (by decide) hp).mpr
      (by rw [shift_constants.2.1]; exact hv.1)
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp hlt))
  have hu : word < 0x4340000000000000 :=
    (F64Order.positive_word_lt_iff word 0x4340000000000000 hp (by decide)).mpr
      (by rw [shift_constants.2.2]; exact hv.2)
  have hs := shift_sub_exact word hl hu
  refine ⟨hl, hu, hs.1, hs.2, ?_⟩
  have hw : value word = (shiftInteger word : ℝ) + 6755399441055744 := by
    rw [value, (shift_word word hl hu).2.2]
    push_cast
    field_simp
    norm_num
  rw [hw] at he
  change |(shiftInteger word : ℝ) - value z| ≤ 1/2
  simpa only [add_sub_add_right_eq_sub] using he

#print axioms shift_rounding
end Project.ExpArm
