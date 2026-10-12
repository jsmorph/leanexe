import LeanExe.ProofKit.F64MulBounds
import LeanExe.ProofKit.F64AddBounds
import LeanExe.ProofKit.F64DivBounds
import LeanExe.ProofKit.RealRoundedError

/-!
One rounded operation on approximations of real numbers.  Each lemma takes words `a` and `b`
within `ea` and `eb` of real numbers `A` and `B` bounded by `ma` and `mb`, and bounds the distance
of the rounded result from the exact operation on `A` and `B`: the propagated input errors plus
the rounding, `u` times a bound on the computed operands' result, plus the underflow term `η` for
products and quotients.  `u` is `unitRoundoff64 = 2 ^ -53` and `η` is
`multiplicationUnderflowEpsilon = 2 ^ -1075`.
-/

namespace LeanExe.ProofKit.F64ApproxStages
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem mul_approx (a b : UInt64) (ha : Finite a) (hb : Finite b) (A B ea eb ma mb : ℝ)
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) (hA : |A| ≤ ma) (hB : |B| ≤ mb)
    (hmax : (ma + ea) * (mb + eb) < (2 : ℝ) ^ 1022) :
    Finite (Wasm.IEEE64.mul a b) ∧
      |value (Wasm.IEEE64.mul a b) - A * B| ≤
        unitRoundoff64 * ((ma + ea) * (mb + eb)) + multiplicationUnderflowEpsilon +
          (ea * (mb + eb) + ma * eb) := by
  have hav : |value a| ≤ ma + ea := by
    have := abs_sub_abs_le_abs_sub (value a) A
    linarith
  have hbv : |value b| ≤ mb + eb := by
    have := abs_sub_abs_le_abs_sub (value b) B
    linarith
  have hp : |value a * value b| ≤ (ma + ea) * (mb + eb) := by
    rw [abs_mul]
    exact mul_le_mul hav hbv (abs_nonneg _) ((abs_nonneg _).trans hav)
  have hs := F64MulBounds.mul_real_mixed a b ha hb (hp.trans_lt hmax)
  refine ⟨hs.1, ?_⟩
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hr : |value (Wasm.IEEE64.mul a b) - value a * value b| ≤
      unitRoundoff64 * ((ma + ea) * (mb + eb)) + multiplicationUnderflowEpsilon :=
    hs.2.trans (by gcongr)
  have hf := RealRoundedError.factor_error _ _ _ _ _ _ hea heb
  have hf' : ea * |value b| + |A| * eb ≤ ea * (mb + eb) + ma * eb := by
    have hea0 : 0 ≤ ea := (abs_nonneg _).trans hea
    have heb0 : 0 ≤ eb := (abs_nonneg _).trans heb
    gcongr
  calc _ ≤ |value (Wasm.IEEE64.mul a b) - value a * value b| + |value a * value b - A * B| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

theorem add_approx (a b : UInt64) (ha : Finite a) (hb : Finite b) (A B ea eb m : ℝ)
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) (hAB : |A + B| ≤ m)
    (hmax : m + ea + eb < (2 : ℝ) ^ 1023) :
    Finite (Wasm.IEEE64.add a b) ∧
      |value (Wasm.IEEE64.add a b) - (A + B)| ≤ unitRoundoff64 * (m + ea + eb) + (ea + eb) := by
  have hs' : |value a + value b - (A + B)| ≤ ea + eb := by
    rw [show value a + value b - (A + B) = (value a - A) + (value b - B) by ring]
    exact (abs_add_le _ _).trans (add_le_add hea heb)
  have hp : |value a + value b| ≤ m + ea + eb := by
    have := abs_sub_abs_le_abs_sub (value a + value b) (A + B)
    linarith
  have hs := F64AddBounds.add_real_relative a b ha hb (hp.trans_lt hmax)
  refine ⟨hs.1, ?_⟩
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hr : |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤
      unitRoundoff64 * (m + ea + eb) := hs.2.trans (by gcongr)
  calc _ ≤ |value (Wasm.IEEE64.add a b) - (value a + value b)| +
        |value a + value b - (A + B)| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

theorem sub_approx (a b : UInt64) (ha : Finite a) (hb : Finite b) (A B ea eb m : ℝ)
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) (hAB : |A - B| ≤ m)
    (hmax : m + ea + eb < (2 : ℝ) ^ 1023) :
    Finite (Wasm.IEEE64.sub a b) ∧
      |value (Wasm.IEEE64.sub a b) - (A - B)| ≤ unitRoundoff64 * (m + ea + eb) + (ea + eb) := by
  have hs' : |value a - value b - (A - B)| ≤ ea + eb := by
    rw [show value a - value b - (A - B) = (value a - A) - (value b - B) by ring]
    exact (abs_sub _ _).trans (add_le_add hea heb)
  have hp : |value a - value b| ≤ m + ea + eb := by
    have := abs_sub_abs_le_abs_sub (value a - value b) (A - B)
    linarith
  have hs := F64AddBounds.sub_real_relative a b ha hb (hp.trans_lt hmax)
  refine ⟨hs.1, ?_⟩
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hr : |value (Wasm.IEEE64.sub a b) - (value a - value b)| ≤
      unitRoundoff64 * (m + ea + eb) := hs.2.trans (by gcongr)
  calc _ ≤ |value (Wasm.IEEE64.sub a b) - (value a - value b)| +
        |value a - value b - (A - B)| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- A rounded quotient of approximations, with the divisor's magnitude at least `lb > eb` and the
exact quotient at most `ρ` in magnitude. -/
theorem div_approx (a b : UInt64) (ha : Finite a) (hb : Finite b) (A B ea eb ρ lb : ℝ)
    (hea : |value a - A| ≤ ea) (heb : |value b - B| ≤ eb) (hlb : lb ≤ |B|) (hlt : eb < lb)
    (hρ : |A| ≤ ρ * |B|) (hmax : ρ + (ea + ρ * eb) / (lb - eb) < (2 : ℝ) ^ 1022) :
    Finite (Wasm.IEEE64.div a b) ∧
      |value (Wasm.IEEE64.div a b) - A / B| ≤
        unitRoundoff64 * (ρ + (ea + ρ * eb) / (lb - eb)) + multiplicationUnderflowEpsilon +
          (ea + ρ * eb) / (lb - eb) := by
  have hea0 : 0 ≤ ea := (abs_nonneg _).trans hea
  have heb0 : 0 ≤ eb := (abs_nonneg _).trans heb
  have hd : 0 < lb - eb := by linarith
  have hBpos : 0 < |B| := by linarith
  have hρ0 : 0 ≤ ρ := by
    by_contra h
    have := mul_neg_of_neg_of_pos (not_le.mp h) hBpos
    have := abs_nonneg A
    linarith
  have hbv : lb - eb ≤ |value b| := by
    have := abs_sub_abs_le_abs_sub B (value b)
    rw [abs_sub_comm] at this
    linarith
  have hbpos : 0 < |value b| := lt_of_lt_of_le hd hbv
  have hb0 : value b ≠ 0 := abs_pos.mp hbpos
  have hB0 : B ≠ 0 := abs_pos.mp hBpos
  have hq : |value a / value b - A / B| ≤ (ea + ρ * eb) / (lb - eb) := by
    have he : value a / value b - A / B = ((value a - A) - (A / B) * (value b - B)) / value b := by
      field_simp
      ring
    rw [he, abs_div]
    rw [div_le_div_iff₀ hbpos hd]
    have hAB : |A / B| ≤ ρ := by
      rw [abs_div, div_le_iff₀ hBpos]
      exact hρ
    have h1 : |(value a - A) - (A / B) * (value b - B)| ≤ ea + ρ * eb := by
      calc _ ≤ |value a - A| + |A / B * (value b - B)| := abs_sub _ _
        _ = |value a - A| + |A / B| * |value b - B| := by rw [abs_mul]
        _ ≤ ea + ρ * eb := by gcongr
    calc |(value a - A) - (A / B) * (value b - B)| * (lb - eb) ≤ (ea + ρ * eb) * (lb - eb) :=
          mul_le_mul_of_nonneg_right h1 hd.le
      _ ≤ (ea + ρ * eb) * |value b| := by gcongr
  have hqv : |value a / value b| ≤ ρ + (ea + ρ * eb) / (lb - eb) := by
    have hAB : |A / B| ≤ ρ := by
      rw [abs_div, div_le_iff₀ hBpos]
      exact hρ
    have := abs_sub_abs_le_abs_sub (value a / value b) (A / B)
    linarith
  have hbm : Wasm.IEEE64.scaledMagnitude b ≠ 0 := by
    intro h
    apply hb0
    simp [value, Wasm.IEEE64.scaledValue, h]
  have hs := F64DivBounds.div_real_mixed a b ha hb hbm (hqv.trans_lt hmax)
  refine ⟨hs.1, ?_⟩
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hr : |value (Wasm.IEEE64.div a b) - value a / value b| ≤
      unitRoundoff64 * (ρ + (ea + ρ * eb) / (lb - eb)) + multiplicationUnderflowEpsilon :=
    hs.2.trans (by gcongr)
  calc _ ≤ |value (Wasm.IEEE64.div a b) - value a / value b| + |value a / value b - A / B| :=
        abs_sub_le _ _ _
    _ ≤ _ := by linarith

#print axioms mul_approx
#print axioms add_approx
#print axioms sub_approx
#print axioms div_approx

end LeanExe.ProofKit.F64ApproxStages
