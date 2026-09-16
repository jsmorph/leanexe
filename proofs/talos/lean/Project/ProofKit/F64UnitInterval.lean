import Project.ProofKit.F64StrictOrder
import Project.ProofKit.F64ArithmeticBounds

namespace Project.ProofKit.F64UnitInterval
open CodeLib.IEEE64 F64Order

set_option exponentiation.threshold 4096

theorem abs_le_one_of_lt_successor (word : UInt64)
    (h : |value word| < 1 + arithmeticEpsilon) : |value word| ≤ 1 := by
  have hone : |value 0x3FF0000000000000| = 1 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hnext : |value 0x3FF0000000000001| = 1 + arithmeticEpsilon := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
      UInt64.toNat_ofNat, arithmeticEpsilon]
  by_cases hb : absBits word ≤ 0x3FF0000000000000
  · have hm := abs_value_mono word 0x3FF0000000000000 (by
      simpa only [show absBits 0x3FF0000000000000 = 0x3FF0000000000000 by decide] using hb)
    simpa only [hone] using hm
  · have hm := abs_value_mono 0x3FF0000000000001 word (by
      rw [UInt64.le_iff_toNat_le]
      rw [UInt64.le_iff_toNat_le] at hb
      change 4607182418800017409 ≤ (absBits word).toNat
      change ¬(absBits word).toNat ≤ 4607182418800017408 at hb
      omega)
    rw [hnext] at hm
    linarith

#print axioms abs_le_one_of_lt_successor
end Project.ProofKit.F64UnitInterval
