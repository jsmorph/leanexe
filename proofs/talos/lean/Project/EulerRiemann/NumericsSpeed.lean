import Project.ProofKit.F64PositiveArithmetic
import Project.ProofKit.F64Absolute

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order
open Project.ProofKit.F64PositiveArithmetic

set_option exponentiation.threshold 4096

theorem speed_error (velocity sound : UInt64) (hv : Finite velocity)
    (hs : positiveBits sound = true) (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (bv : |value velocity| ≤ 2 * M^2) (bs : value sound ≤ 14 * M^2) :
    let speed := Wasm.IEEE64.add (absBits velocity) sound
    positiveBits speed = true ∧
    (|value velocity| + value sound) / 2 ≤ value speed ∧ value speed ≤ 32 * M^2 ∧
    |value speed - (|value velocity| + value sound)| ≤
      unitRoundoff64 * (|value velocity| + value sound) := by
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hp := positiveBits_spec sound hs
  have hsum : 0 < value (absBits velocity) + value sound := by
    rw [absBits_value]
    exact add_pos_of_nonneg_of_pos (abs_nonneg _) hp.2
  have hupper : value (absBits velocity) + value sound ≤ 16 * M^2 := by
    rw [absBits_value]
    linarith only [bv, bs]
  have hmax : value (absBits velocity) + value sound < (2 : ℝ)^1023 := by
    calc
      _ ≤ 16 * M^2 := hupper
      _ ≤ 16 * ((2 : ℝ)^100)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 2) (by norm_num)
      _ < (2 : ℝ)^1023 := by norm_num
  obtain ⟨hpos, hlo, hhi, herr⟩ := add_positive (absBits velocity) sound
    (absBits_finite velocity hv) hp.1 hsum hmax
  rw [absBits_value] at hlo herr
  exact ⟨hpos, hlo, by linarith only [hhi, hupper], herr⟩

#print axioms speed_error
end Project.EulerRiemann.Numerics
