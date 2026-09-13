import Project.ProofKit.F64PositiveArithmetic
import Project.ProofKit.RealSqrtError

namespace Project.ProofKit.F64SqrtComposition
open CodeLib.IEEE64

theorem input_error (a : UInt64) (ha : F64Order.positiveBits a = true)
    (exactValue delta : ℝ) (he : 0 < exactValue) (hd : delta ≤ 1)
    (herr : |value a - exactValue| ≤ delta * exactValue) :
    F64Order.positiveBits (Wasm.IEEE64.sqrt a) = true ∧
    |value (Wasm.IEEE64.sqrt a) - Real.sqrt exactValue| ≤
      (delta + arithmeticEpsilon) * Real.sqrt exactValue := by
  obtain ⟨hf, hs, hz⟩ := F64PositiveArithmetic.positive_input a ha
  have hp := (F64Order.positiveBits_spec a ha).2
  have hr := RealSqrtError.relative_error (value a) exactValue delta hp.le he herr
  have hroot := Real.sqrt_pos.mpr he
  have hupper : Real.sqrt (value a) ≤ 2 * Real.sqrt exactValue := by
    have hu := (abs_le.mp hr).2
    have hb := mul_le_mul_of_nonneg_right hd hroot.le
    linarith only [hu, hb]
  have hround := (F64SqrtBounds.sqrt_real_relative a hf hz hs).2
  have heps : 2 * unitRoundoff64 = arithmeticEpsilon := by
    norm_num [unitRoundoff64, arithmeticEpsilon]
  have hb := mul_le_mul_of_nonneg_left hupper (by norm_num [unitRoundoff64] : 0 ≤ unitRoundoff64)
  have hroundBound : |value (Wasm.IEEE64.sqrt a) - Real.sqrt (value a)| ≤
      arithmeticEpsilon * Real.sqrt exactValue := by
    calc
      _ ≤ unitRoundoff64 * Real.sqrt (value a) := hround
      _ ≤ unitRoundoff64 * (2 * Real.sqrt exactValue) := hb
      _ = arithmeticEpsilon * Real.sqrt exactValue := by rw [← mul_assoc, mul_comm unitRoundoff64, heps]
  refine ⟨(F64PositiveArithmetic.sqrt_positive a hf hz hs).1, ?_⟩
  calc
    _ ≤ |value (Wasm.IEEE64.sqrt a) - Real.sqrt (value a)| +
        |Real.sqrt (value a) - Real.sqrt exactValue| := abs_sub_le _ _ _
    _ ≤ arithmeticEpsilon * Real.sqrt exactValue + delta * Real.sqrt exactValue :=
      add_le_add hroundBound hr
    _ = (delta + arithmeticEpsilon) * Real.sqrt exactValue := by ring

#print axioms input_error
end Project.ProofKit.F64SqrtComposition
