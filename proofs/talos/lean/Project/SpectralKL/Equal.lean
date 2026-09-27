import Project.ProofKit.F64ArithmeticBounds

namespace Project.SpectralKL
open CodeLib.IEEE64 Project.ProofKit.F64ArithmeticBounds

set_option exponentiation.threshold 4096

/-- Pure IEEE model of the first executable iteration. -/
def equalMomentsBits (d : UInt64) : UInt64 :=
  Wasm.IEEE64.mul 0x3FE0000000000000 (Wasm.IEEE64.mul d d)

theorem half_value : value 0x3FE0000000000000 = 1 / 2 := by
  norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
    Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

/-- A uniform absolute bound includes subnormal inputs and underflow. -/
theorem equalMoments_error (d : UInt64) (hd : Finite d) (bd : |value d| ≤ 1) :
    Finite (equalMomentsBits d) ∧
      |value (equalMomentsBits d) - value d ^ 2 / 2| ≤ 2 * arithmeticEpsilon := by
  have bp : |value d * value d| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (value d)]
  obtain ⟨hf, he⟩ := mul_error d d hd hd 1 (by norm_num) (by norm_num) bp
  have hm := magnitude_of_error _ _ _ _ he bp
  have be : arithmeticEpsilon ≤ 1 := by norm_num [arithmeticEpsilon]
  have bh : |value 0x3FE0000000000000 * value (Wasm.IEEE64.mul d d)| ≤ 1 := by
    rw [half_value, abs_mul]
    norm_num
    nlinarith
  obtain ⟨hg, eg⟩ := mul_error 0x3FE0000000000000 (Wasm.IEEE64.mul d d)
    (by unfold CodeLib.IEEE64.Finite; decide) hf 1 (by norm_num) (by norm_num) bh
  refine ⟨hg, ?_⟩
  rw [half_value] at eg
  have h₁ := abs_le.mp he
  have h₂ := abs_le.mp eg
  unfold equalMomentsBits
  apply abs_le.mpr
  constructor <;> nlinarith [epsilon_pos]

#print axioms equalMoments_error
end Project.SpectralKL
