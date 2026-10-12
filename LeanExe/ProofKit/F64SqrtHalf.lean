import LeanExe.ProofKit.F64SqrtBounds

/-!
The rounded square root lies within half a spacing of the binade below a bound of the exact root:
when `√(value a) < 2 ^ (53 + g)` scaled units, the result lies within `2 ^ g / 2` scaled units, as
`F64HalfUlp.add_half` states for sums.  The proof follows `F64SqrtRounding.sqrt_relative` up to
the integer error `CodeLib.IEEE32.roundSqrtIntegral_real_error`, whose unit `2 ^ outputShift` is at
most `2 ^ g`.
-/

namespace LeanExe.ProofKit.F64SqrtHalf
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem sqrt_half_scaled (magnitude : Nat) (hm : magnitude ≠ 0) (hmax : magnitude < 2^2098)
    (g : ℕ) (hg : Real.sqrt (magnitude * 2^1074 : Nat) < 2 ^ (53 + g)) :
    Finite (Wasm.IEEE64.roundSqrtMagnitude magnitude) ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundSqrtMagnitude magnitude) = false ∧
    |(Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundSqrtMagnitude magnitude) : ℝ) -
      Real.sqrt (magnitude * 2^1074 : Nat)| ≤ 2 ^ g / 2 := by
  let radicand := magnitude * 2^1074
  let rootFloor := Nat.sqrt radicand
  let outputShift := Nat.log2 rootFloor - 52
  let rounded := Wasm.IEEE32.roundSqrtIntegral radicand outputShift
  let candidate := rounded * 2^outputShift
  have hradicandLower : 2^1074 ≤ radicand := by
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm)
  have hradicandUpper : radicand < 2^3172 := by
    calc
      radicand < 2^2098 * 2^1074 := Nat.mul_lt_mul_of_pos_right hmax (by positivity)
      _ = 2^3172 := by rw [← pow_add]
  have hrootLower : 2^537 ≤ rootFloor := by
    apply Nat.le_sqrt'.2
    simpa only [← pow_mul] using hradicandLower
  have hrootUpper : rootFloor < 2^1586 := by
    apply Nat.sqrt_lt'.2
    simpa only [← pow_mul] using hradicandUpper
  have hrootNe : rootFloor ≠ 0 := by omega
  have hlogLower : 537 ≤ Nat.log2 rootFloor := (Nat.le_log2 hrootNe).2 hrootLower
  have hlogUpper : Nat.log2 rootFloor < 1586 := (Nat.log2_lt hrootNe).2 hrootUpper
  have hshiftMax : outputShift ≤ 1533 := by dsimp [outputShift]; omega
  have hshiftEq : 52 + outputShift = Nat.log2 rootFloor := by dsimp [outputShift]; omega
  have hpowLower : 2^52 * 2^outputShift ≤ rootFloor := by
    rw [← pow_add, hshiftEq]
    exact Nat.log2_self_le hrootNe
  have hpowUpper : rootFloor < 2^53 * 2^outputShift := by
    rw [← pow_add, show 53 + outputShift = Nat.log2 rootFloor + 1 by omega]
    exact Nat.lt_log2_self
  have hroundBounds := CodeLib.IEEE32.roundSqrtIntegral_bounds radicand outputShift
  change rootFloor / 2^outputShift ≤ rounded ∧ rounded ≤ rootFloor / 2^outputShift + 1
    at hroundBounds
  have hquotLower : 2^52 ≤ rootFloor / 2^outputShift :=
    (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : rootFloor / 2^outputShift < 2^53 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hroundedLower : 2^52 ≤ rounded := by omega
  have hroundedUpper : rounded ≤ 2^53 := by omega
  have hrepresentable : roundedMagnitude candidate = candidate :=
    F64DyadicBounds.roundedMagnitude_shifted rounded outputShift hroundedLower hroundedUpper
  have hcandidateMax : candidate < 2^2097 := by
    calc
      candidate ≤ 2^53 * 2^1533 :=
        Nat.mul_le_mul hroundedUpper (Nat.pow_le_pow_right (by omega) hshiftMax)
      _ = 2^1586 := by rw [← pow_add]
      _ < 2^2097 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpack := F64PackRelative.pack_spec false candidate hcandidateMax
  have hactual : Wasm.IEEE64.roundSqrtMagnitude magnitude =
      Wasm.IEEE64.roundScaledMagnitude false candidate := by
    simp only [Wasm.IEEE64.roundSqrtMagnitude, beq_iff_eq, if_neg hm]
    rfl
  have herr := CodeLib.IEEE32.roundSqrtIntegral_real_error radicand outputShift
  -- the unit is at most `2 ^ g`
  have hrootReal : (rootFloor : ℝ) ≤ Real.sqrt radicand := Real.nat_sqrt_le_real_sqrt
  have hrootG : rootFloor < 2 ^ (53 + g) := by
    have h : (rootFloor : ℝ) < 2 ^ (53 + g) := lt_of_le_of_lt hrootReal hg
    exact_mod_cast h
  have hlogG : Nat.log2 rootFloor < 53 + g := (Nat.log2_lt hrootNe).2 hrootG
  have hshiftG : outputShift ≤ g := by dsimp [outputShift]; omega
  have hunit : (2 : ℝ) ^ outputShift / 2 ≤ 2 ^ g / 2 := by
    have : (2 : ℝ) ^ outputShift ≤ 2 ^ g := pow_le_pow_right₀ (by norm_num) hshiftG
    linarith
  rw [hactual]
  refine ⟨hpack.1, hpack.2.2, ?_⟩
  rw [hpack.2.1, hrepresentable]
  have h2 : |(candidate : ℝ) - Real.sqrt (radicand : ℝ)| ≤ (2 : ℝ) ^ outputShift / 2 := by
    simpa only [candidate, rounded, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using herr
  exact h2.trans hunit

/-- `√(value a)` below `2 ^ (53 + g)` scaled units: the rounded root lies within `2 ^ g / 2`. -/
theorem sqrt_half (a : UInt64) (ha : Finite a) (ha0 : Wasm.IEEE64.scaledMagnitude a ≠ 0)
    (hsign : Wasm.IEEE64.sign a = false) (g : ℕ)
    (hS : Real.sqrt (value a) < 2 ^ (53 + g) / 2 ^ 1074) :
    Finite (Wasm.IEEE64.sqrt a) ∧
      |value (Wasm.IEEE64.sqrt a) - Real.sqrt (value a)| ≤ 2 ^ g / 2 / 2 ^ 1074 := by
  let magnitude := Wasm.IEEE64.scaledMagnitude a
  have hmax : magnitude < 2^2098 :=
    (F64NormalizeTiny.scaledMagnitude_bound a).trans_le
      (Nat.pow_le_pow_right (by omega)
        (by have := F64Admissibility.finite_exponent_bound a ha; omega))
  have hscalePos : (0 : ℝ) < (2 : ℝ)^1074 := by positivity
  have hsqrtScale : Real.sqrt ((2 : ℝ)^1074) = (2 : ℝ)^537 := by
    rw [show (2 : ℝ)^1074 = ((2 : ℝ)^537)^2 by rw [← pow_mul]]
    exact Real.sqrt_sq (by positivity)
  have hsqrtScaled : Real.sqrt ((magnitude : ℝ) / (2 : ℝ)^1074) =
      Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074) / (2 : ℝ)^1074 := by
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ magnitude),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ magnitude), hsqrtScale]
    field_simp
  have hvalueA : value a = (magnitude : ℝ) / (2 : ℝ)^1074 := by
    simp [value, magnitude, Wasm.IEEE64.scaledValue, hsign]
  have hg : Real.sqrt (magnitude * 2^1074 : Nat) < 2 ^ (53 + g) := by
    rw [hvalueA, hsqrtScaled, div_lt_div_iff_of_pos_right hscalePos] at hS
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hS
  have hs := sqrt_half_scaled magnitude ha0 hmax g hg
  rw [CodeLib.IEEE64.sqrt_positive_finite a ha ha0 hsign]
  refine ⟨hs.1, ?_⟩
  have hvalueResult : value (Wasm.IEEE64.roundSqrtMagnitude magnitude) =
      (Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundSqrtMagnitude magnitude) : ℝ) /
        (2 : ℝ)^1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hs.2.1]
  have heq : value (Wasm.IEEE64.roundSqrtMagnitude magnitude) - Real.sqrt (value a) =
      ((Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundSqrtMagnitude magnitude) : ℝ) -
        Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074)) / (2 : ℝ)^1074 := by
    rw [hvalueA, hvalueResult, hsqrtScaled]
    ring
  rw [heq, abs_div, abs_of_pos hscalePos]
  have herr : |(Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundSqrtMagnitude magnitude) : ℝ) -
      Real.sqrt ((magnitude : ℝ) * (2 : ℝ)^1074)| ≤ 2 ^ g / 2 := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hs.2.2
  exact div_le_div_of_nonneg_right herr hscalePos.le

#print axioms sqrt_half_scaled
#print axioms sqrt_half

end LeanExe.ProofKit.F64SqrtHalf
