import Project.ProofKit.F64StrictOrder
import Project.ProofKit.F64ArithmeticBounds

namespace Project.ProofKit.F64UnitInterval
open CodeLib.IEEE64 F64Order

set_option exponentiation.threshold 4096

theorem abs_le_of_lt_next (word bound next : UInt64)
    (hb : absBits bound = bound) (hn : absBits next = next)
    (hadj : bound.toNat+1 = next.toNat)
    (h : |value word| < |value next|) : |value word| ≤ |value bound| := by
  by_cases hw : absBits word ≤ bound
  · exact abs_value_mono word bound (by simpa only [hb] using hw)
  · have hm := abs_value_mono next word (by
      rw [hn, UInt64.le_iff_toNat_le]
      rw [UInt64.le_iff_toNat_le] at hw
      omega)
    linarith

theorem abs_le_two_of_lt_successor (word : UInt64)
    (h : |value word| < 2 + 2*arithmeticEpsilon) : |value word| ≤ 2 := by
  have hb : |value 0x4000000000000000| = 2 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hn : |value 0x4000000000000001| = 2 + 2*arithmeticEpsilon := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
      UInt64.toNat_ofNat, arithmeticEpsilon]
  rw [← hb]
  exact abs_le_of_lt_next word 0x4000000000000000 0x4000000000000001
    (by decide) (by decide) (by decide) (by simpa only [hn] using h)

theorem abs_le_sixteen_of_lt_successor (word : UInt64)
    (h : |value word| < 16 + 16*arithmeticEpsilon) : |value word| ≤ 16 := by
  have hb : |value 0x4030000000000000| = 16 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hn : |value 0x4030000000000001| = 16 + 16*arithmeticEpsilon := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
      UInt64.toNat_ofNat, arithmeticEpsilon]
  rw [← hb]
  exact abs_le_of_lt_next word 0x4030000000000000 0x4030000000000001
    (by decide) (by decide) (by decide) (by simpa only [hn] using h)

theorem abs_le_one_of_lt_successor (word : UInt64)
    (h : |value word| < 1 + arithmeticEpsilon) : |value word| ≤ 1 := by
  have hone : |value 0x3FF0000000000000| = 1 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hnext : |value 0x3FF0000000000001| = 1 + arithmeticEpsilon := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
      UInt64.toNat_ofNat, arithmeticEpsilon]
  rw [← hone]
  exact abs_le_of_lt_next word 0x3FF0000000000000 0x3FF0000000000001
    (by decide) (by decide) (by decide) (by simpa only [hnext] using h)

theorem abs_le_eight_of_lt_successor (word : UInt64)
    (h : |value word| < 8 + 8*arithmeticEpsilon) : |value word| ≤ 8 := by
  have hone : |value 0x4020000000000000| = 8 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hnext : |value 0x4020000000000001| = 8 + 8*arithmeticEpsilon := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction,
      UInt64.toNat_ofNat, arithmeticEpsilon]
  rw [← hone]
  exact abs_le_of_lt_next word 0x4020000000000000 0x4020000000000001
    (by decide) (by decide) (by decide) (by simpa only [hnext] using h)

#print axioms abs_le_one_of_lt_successor
end Project.ProofKit.F64UnitInterval
