import Verified.Examples.Expm1KernelPoly
import LeanExe.ProofKit.F64ApproxStages
import LeanExe.ProofKit.F64NearestSum
import LeanExe.ProofKit.F64PowerScale

/-!
The rounding errors of the shared part of fdlibm's `expm1` kernel, for `abs(x) ≤ 0.3466`: `x/2`,
`hxs = x (x/2)`, the polynomial `r1`, `t = 3 - r1 x/2`, the numerator `r1 - t`, the denominator
`6 - x t`, their quotient, and `e = hxs (r1 - t)/(6 - x t)`.  Each is compared with the same
expression in exact arithmetic at `X = value x`, with `P = polyValue (X ^ 2 / 2)`: `T = 3 - P X/2`,
`Nm = P - T`, `Dn = 6 - X T`, and `eValue X = (X ^ 2/2) Nm/Dn`.  The final bound is
`abs(e - eValue X) ≤ (27/10) u X ^ 2/2 + 4 η`.  Bounds near `1` use the half spacing of the result's
binade, and the others the relative error of the rounding.
-/

namespace Verified.Examples.Expm1KernelInner
open CodeLib.IEEE64 LeanExe.ProofKit F64ApproxStages Expm1KernelPoly

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem u_value : u = 1 / 2 ^ 53 := rfl
theorem eta_value : η = 1 / 2 ^ 1075 := rfl

/-! ### Constants -/

theorem const_values :
    value Expm1Words.one = 1 ∧ value Expm1Words.half = 1 / 2 ∧ value Expm1Words.two = 2 ∧
      value Expm1Words.three = 3 ∧ value Expm1Words.six = 6 ∧ value Expm1Words.negTwo = -2 ∧
      value Expm1Words.negQuarter = -1 / 4 := by
  have h1 : Wasm.IEEE64.scaledValue Expm1Words.one = 2 ^ 1074 := by decide +kernel
  have h2 : Wasm.IEEE64.scaledValue Expm1Words.half = 2 ^ 1073 := by decide +kernel
  have h3 : Wasm.IEEE64.scaledValue Expm1Words.two = 2 ^ 1075 := by decide +kernel
  have h4 : Wasm.IEEE64.scaledValue Expm1Words.three = 3 * 2 ^ 1074 := by decide +kernel
  have h5 : Wasm.IEEE64.scaledValue Expm1Words.six = 6 * 2 ^ 1074 := by decide +kernel
  have h6 : Wasm.IEEE64.scaledValue Expm1Words.negTwo = -2 ^ 1075 := by decide +kernel
  have h7 : Wasm.IEEE64.scaledValue Expm1Words.negQuarter = -2 ^ 1072 := by decide +kernel
  simp only [value, h1, h2, h3, h4, h5, h6, h7]
  norm_num

theorem const_finite :
    Finite Expm1Words.one ∧ Finite Expm1Words.half ∧ Finite Expm1Words.two ∧
      Finite Expm1Words.three ∧ Finite Expm1Words.six ∧ Finite Expm1Words.negTwo ∧
      Finite Expm1Words.negQuarter ∧ Finite Expm1Words.Q1 ∧ Finite Expm1Words.Q2 ∧
      Finite Expm1Words.Q3 ∧ Finite Expm1Words.Q4 ∧ Finite Expm1Words.Q5 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem coefficient_rat :
    PolyBound.qabs (PolyBound.ratOfWord Expm1Words.Q1) ≤ 1 / 30 ∧
      PolyBound.qabs (PolyBound.ratOfWord Expm1Words.Q2) ≤ 16 / 10000 ∧
      PolyBound.qabs (PolyBound.ratOfWord Expm1Words.Q3) ≤ 8 / 100000 ∧
      PolyBound.qabs (PolyBound.ratOfWord Expm1Words.Q4) ≤ 41 / 10000000 ∧
      PolyBound.qabs (PolyBound.ratOfWord Expm1Words.Q5) ≤ 21 / 100000000 := by
  decide +kernel

theorem coefficient_bounds :
    |value Expm1Words.Q1| ≤ 1 / 30 ∧ |value Expm1Words.Q2| ≤ 16 / 10000 ∧
      |value Expm1Words.Q3| ≤ 8 / 100000 ∧ |value Expm1Words.Q4| ≤ 41 / 10000000 ∧
      |value Expm1Words.Q5| ≤ 21 / 100000000 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := coefficient_rat
  simp only [← PolyBound.ratOfWord_cast, ← PolyBound.qabs_cast]
  refine ⟨((Rat.cast_le (K := ℝ)).mpr h1).trans (le_of_eq (by norm_num)),
    ((Rat.cast_le (K := ℝ)).mpr h2).trans (le_of_eq (by norm_num)),
    ((Rat.cast_le (K := ℝ)).mpr h3).trans (le_of_eq (by norm_num)),
    ((Rat.cast_le (K := ℝ)).mpr h4).trans (le_of_eq (by norm_num)),
    ((Rat.cast_le (K := ℝ)).mpr h5).trans (le_of_eq (by norm_num))⟩

/-- `P z = 1 + z (Q1 + z (Q2 + z (Q3 + z (Q4 + z Q5))))`. -/
theorem polyValue_eq (z : ℝ) :
    polyValue z = 1 + z * (value Expm1Words.Q1 + z * (value Expm1Words.Q2 + z *
      (value Expm1Words.Q3 + z * (value Expm1Words.Q4 + z * value Expm1Words.Q5)))) := by
  simp only [polyValue, kernelP, PolyBound.eval_cons, PolyBound.eval_nil, PolyBound.ratOfWord_cast]
  push_cast
  ring

/-! ### The first products -/

theorem hfx_spec (x : UInt64) (hxf : Finite x) :
    Finite (Expm1Words.hfx x) ∧ |value (Expm1Words.hfx x) - value x / 2| ≤ 2 * η := by
  have hhalf : Expm1Words.half = Wasm.IEEE64.encodeFinite false 1022 0 := by decide
  unfold Expm1Words.hfx
  rw [hhalf]
  by_cases he : 2 ≤ Wasm.IEEE64.exponent x
  · have h := F64PowerScale.mul_power_finite 1022 x (by norm_num) (by norm_num) hxf (by omega)
      (by omega) (by
        have : Wasm.IEEE64.exponent x < 2048 := Nat.mod_lt _ (by norm_num)
        have hf := hxf
        simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
        omega)
    refine ⟨h.1, ?_⟩
    rw [h.2]
    have : (2 : ℝ) ^ ((1022 : ℕ) - 1023 : ℤ) = 1 / 2 := by norm_num
    rw [this]
    have hη : (0 : ℝ) ≤ 2 * η := by norm_num [multiplicationUnderflowEpsilon]
    simpa [div_eq_mul_inv, mul_comm] using hη
  · have hsmall : |value x| ≤ 2 ^ 53 / 2 ^ 1074 := by
      have hm : Wasm.IEEE64.scaledMagnitude x ≤ 2 ^ 53 := by
        have hf : Wasm.IEEE64.fraction x < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
        unfold Wasm.IEEE64.scaledMagnitude
        by_cases h0 : Wasm.IEEE64.exponent x = 0
        · simp only [h0, beq_self_eq_true, ite_true]
          omega
        · have h1 : Wasm.IEEE64.exponent x = 1 := by omega
          simp only [h1, beq_iff_eq, one_ne_zero, ite_false, Nat.sub_self, pow_zero, mul_one]
          omega
      have hv : |value x| = (Wasm.IEEE64.scaledMagnitude x : ℝ) / 2 ^ 1074 := by
        rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
          ← CodeLib.IEEE64.natAbs_scaledValue, Nat.cast_natAbs, Int.cast_abs]
      rw [hv]
      gcongr
      exact_mod_cast hm
    have hhv : value (Wasm.IEEE64.encodeFinite false 1022 0) = 1 / 2 := by
      rw [← hhalf]
      exact const_values.2.1
    have h := F64MulBounds.mul_real_mixed (Wasm.IEEE64.encodeFinite false 1022 0) x
      (by rw [← hhalf]; exact const_finite.2.1) hxf (by
        rw [hhv, abs_mul]
        calc |(1 / 2 : ℝ)| * |value x| ≤ 1 * (2 ^ 53 / 2 ^ 1074) := by
              gcongr
              norm_num
          _ < 2 ^ 1022 := by norm_num)
    refine ⟨h.1, ?_⟩
    rw [hhv] at h
    have h2 := h.2
    rw [show (1 / 2 : ℝ) * value x = value x / 2 by ring] at h2
    refine h2.trans ?_
    rw [abs_div, abs_two]
    have : |value x| / 2 ≤ 2 ^ 53 / 2 ^ 1074 / 2 := by gcongr
    calc u * (|value x| / 2) + η ≤ (1 / 2 ^ 53) * (2 ^ 53 / 2 ^ 1074 / 2) + η := by
          rw [u_value]
          gcongr
      _ = 2 * η := by rw [eta_value]; norm_num

theorem hxs_spec (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 1) :
    Finite (Expm1Words.hxs x) ∧
      |value (Expm1Words.hxs x) - value x ^ 2 / 2| ≤ u * (value x ^ 2 / 2) + 4 * η := by
  obtain ⟨hf, he⟩ := hfx_spec x hxf
  have hm := mul_approx x (Expm1Words.hfx x) hxf hf (value x) (value x / 2) 0 (2 * η) 1
    (1 / 2) (by simp) he hx (by rw [abs_div, abs_two]; linarith)
    (by norm_num [multiplicationUnderflowEpsilon])
  refine ⟨hm.1, ?_⟩
  -- A sharper bound than `mul_approx` gives: the exact product is `X ^ 2/2 + X δ`.
  have hp : |value x * value (Expm1Words.hfx x) - value x ^ 2 / 2| ≤ 2 * η := by
    rw [show value x * value (Expm1Words.hfx x) - value x ^ 2 / 2 =
      value x * (value (Expm1Words.hfx x) - value x / 2) by ring, abs_mul]
    calc |value x| * |value (Expm1Words.hfx x) - value x / 2| ≤ 1 * (2 * η) := by
          gcongr
      _ = 2 * η := one_mul _
  have hpm : |value x * value (Expm1Words.hfx x)| ≤ value x ^ 2 / 2 + 2 * η := by
    have := abs_sub_abs_le_abs_sub (value x * value (Expm1Words.hfx x)) (value x ^ 2 / 2)
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ value x ^ 2 / 2)] at this
    linarith
  have hx2 : value x ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hx
  have h2η : 2 * η ≤ 1 := by rw [eta_value]; norm_num
  have h32 : (3 / 2 : ℝ) < 2 ^ 1022 := by norm_num
  have hr := F64MulBounds.mul_real_mixed x (Expm1Words.hfx x) hxf hf (by
    refine hpm.trans_lt ?_
    linarith)
  have hu : (0 : ℝ) ≤ u := by norm_num [unitRoundoff64]
  have hu1 : u ≤ 1 := by norm_num [unitRoundoff64]
  have hη : (0 : ℝ) ≤ η := by norm_num [multiplicationUnderflowEpsilon]
  calc |value (Expm1Words.hxs x) - value x ^ 2 / 2| ≤
      |value (Expm1Words.hxs x) - value x * value (Expm1Words.hfx x)| +
        |value x * value (Expm1Words.hfx x) - value x ^ 2 / 2| := abs_sub_le _ _ _
    _ ≤ (u * (value x ^ 2 / 2 + 2 * η) + η) + 2 * η := by
        have h1 := mul_le_mul_of_nonneg_left hpm hu
        have hr2 : |value (Expm1Words.hxs x) - value x * value (Expm1Words.hfx x)| ≤
            u * |value x * value (Expm1Words.hfx x)| + η := hr.2
        linarith
    _ ≤ u * (value x ^ 2 / 2) + 4 * η := by
        have h : u * (2 * η) ≤ η := by rw [u_value, eta_value]; norm_num
        rw [mul_add]
        linarith

#print axioms const_values
#print axioms coefficient_bounds
#print axioms polyValue_eq
#print axioms hfx_spec
#print axioms hxs_spec

end Verified.Examples.Expm1KernelInner
