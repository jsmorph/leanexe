import Project.ProofKit.F32DyadicReal
import Project.ProofKit.F64ExactShift

namespace Project.WGSL.Precision
open Project.ProofKit

set_option exponentiation.threshold 4096

/-- Pure conversion model for finite binary64 inputs, with one ties-to-even
rounding and gradual underflow. Nonfinite inputs are outside this interface. -/
def demote (a : UInt64) : UInt32 :=
  Wasm.IEEE32.roundDyadicMagnitude (Wasm.IEEE64.sign a) (Wasm.IEEE64.scaledMagnitude a) 925

/-- Pure conversion model for finite binary32 inputs. -/
def promote (a : UInt32) : UInt64 :=
  Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE32.sign a) (Wasm.IEEE32.scaledMagnitude a * 2^925)

theorem input32_bound (a : UInt32) (ha : CodeLib.IEEE32.Finite a) :
    Wasm.IEEE32.scaledMagnitude a < 2^277 := by
  have he := CodeLib.IEEE32.finite_exponent_lt ha
  have hf := CodeLib.IEEE32.fraction_lt a
  simp only [Wasm.IEEE32.scaledMagnitude, beq_iff_eq]
  split
  · omega
  · calc
      (2^23 + Wasm.IEEE32.fraction a) * 2^(Wasm.IEEE32.exponent a-1) <
          2^24 * 2^(Wasm.IEEE32.exponent a-1) := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      _ ≤ 2^24 * 2^253 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ = 2^277 := by rw [← pow_add]

theorem promote_exact_magnitude (a : UInt32) :
    CodeLib.IEEE64.roundedMagnitude (Wasm.IEEE32.scaledMagnitude a * 2^925) =
      Wasm.IEEE32.scaledMagnitude a * 2^925 := by
  have hf := CodeLib.IEEE32.fraction_lt a
  simp only [Wasm.IEEE32.scaledMagnitude, beq_iff_eq]
  split
  · exact F64ExactShift.rounded_shift _ _ (by omega)
  · rw [Nat.mul_assoc, ← pow_add]
    exact F64ExactShift.rounded_shift _ _ (by omega)

theorem promote_spec (a : UInt32) (ha : CodeLib.IEEE32.Finite a) :
    CodeLib.IEEE64.Finite (promote a) ∧
    Wasm.IEEE64.scaledMagnitude (promote a) = Wasm.IEEE32.scaledMagnitude a * 2^925 ∧
    Wasm.IEEE64.sign (promote a) = Wasm.IEEE32.sign a := by
  have hb := input32_bound a ha
  have hmax : Wasm.IEEE32.scaledMagnitude a * 2^925 < 2^2097 := by
    calc
      _ < 2^277 * 2^925 := Nat.mul_lt_mul_of_pos_right hb (by positivity)
      _ = 2^1202 := by rw [← pow_add]
      _ < 2^2097 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hs := F64Packing.pack_spec (Wasm.IEEE32.sign a) _ hmax
  rw [promote_exact_magnitude] at hs
  exact hs

theorem promote_value (a : UInt32) (ha : CodeLib.IEEE32.Finite a) :
    CodeLib.IEEE64.value (promote a) = CodeLib.IEEE32.value a := by
  have hs := promote_spec a ha
  simp only [CodeLib.IEEE64.value, CodeLib.IEEE32.value,
    Wasm.IEEE64.scaledValue, Wasm.IEEE32.scaledValue, hs.2.1, hs.2.2]
  split <;> push_cast <;> norm_num <;> ring

theorem input64_abs (a : UInt64) :
    |CodeLib.IEEE64.value a| = (Wasm.IEEE64.scaledMagnitude a : ℝ) / 2^1074 := by
  simp only [CodeLib.IEEE64.value, Wasm.IEEE64.scaledValue]
  split <;> simp [abs_div]

theorem demote_error (a : UInt64) (_ha : CodeLib.IEEE64.Finite a)
    (hb : |CodeLib.IEEE64.value a| < (2:ℝ)^127) :
    CodeLib.IEEE32.Finite (demote a) ∧
    |CodeLib.IEEE32.value (demote a) - CodeLib.IEEE64.value a| ≤
      F32AddBounds.unitRoundoff * |CodeLib.IEEE64.value a| + F32MulBounds.multiplicationUnderflowEpsilon := by
  have hmax : Wasm.IEEE64.scaledMagnitude a < 2^1201 := by
    rw [input64_abs] at hb
    have h := (div_lt_iff₀ (by positivity : (0:ℝ) < 2^1074)).mp hb
    rw [← pow_add] at h
    exact_mod_cast h
  have heq : F32DyadicReal.exactValue (Wasm.IEEE64.sign a) (Wasm.IEEE64.scaledMagnitude a) 925 =
      CodeLib.IEEE64.value a := by
    simp only [F32DyadicReal.exactValue, CodeLib.IEEE64.value, Wasm.IEEE64.scaledValue]
    split <;> push_cast <;> rfl
  have hs := F32DyadicReal.real_mixed (Wasm.IEEE64.sign a) (Wasm.IEEE64.scaledMagnitude a)
    925 (by decide) hmax
  simpa only [demote, heq] using hs

#print axioms promote_spec
#print axioms promote_value
#print axioms demote_error
end Project.WGSL.Precision
