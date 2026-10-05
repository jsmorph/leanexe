import Project.ProofKit.F64RounderEnclosure
import CodeLib.IEEE64.Operations

namespace Project.ProofKit.F64Adjacent
open CodeLib.IEEE64
set_option exponentiation.threshold 4096

theorem sqrt_magnitude_enclosure (n : Nat)
    (hf : Finite (Wasm.IEEE64.roundSqrtMagnitude n)) :
    value (nextDown (Wasm.IEEE64.roundSqrtMagnitude n)) ≤
      Real.sqrt ((n*2^1074:Nat):ℝ)/(2:ℝ)^1074 ∧
    Real.sqrt ((n*2^1074:Nat):ℝ)/(2:ℝ)^1074 ≤
      value (nextUp (Wasm.IEEE64.roundSqrtMagnitude n)) := by
  by_cases hn : n = 0
  · subst n
    simpa [Wasm.IEEE64.roundSqrtMagnitude, Wasm.IEEE64.signMask] using zero_enclosure false
  let radicand := n*2^1074
  let shift := Nat.log2 (Nat.sqrt radicand)-52
  let rounded := Wasm.IEEE32.roundSqrtIntegral radicand shift
  have ha : Wasm.IEEE64.roundSqrtMagnitude n =
      Wasm.IEEE64.roundScaledMagnitude false (rounded*2^shift) := by
    simp only [Wasm.IEEE64.roundSqrtMagnitude, beq_iff_eq, ite_eq_right hn]
    rfl
  have hw := significand_window (Nat.sqrt radicand) 0
  simp only [Nat.zero_add] at hw
  have hr := CodeLib.IEEE32.roundSqrtIntegral_bounds radicand shift
  have hu : rounded ≤ 2^53 := by dsimp only [rounded, shift] at *; omega
  have hl : shift = 0 ∨ 2^52 ≤ rounded := hw.2.imp id (fun h => h.trans hr.1)
  rw [ha] at hf ⊢
  exact candidate_enclosure false rounded shift _ hf (Real.sqrt_nonneg _) hu hl
    (CodeLib.IEEE32.roundSqrtIntegral_real_error radicand shift)

theorem sqrt_scaled_value (n : Nat) :
    Real.sqrt ((n:ℝ)/(2:ℝ)^1074) = Real.sqrt ((n*2^1074:Nat):ℝ)/(2:ℝ)^1074 := by
  have hs : Real.sqrt ((2:ℝ)^1074) = (2:ℝ)^537 := by
    rw [show (2:ℝ)^1074 = ((2:ℝ)^537)^2 by rw [← pow_mul]]
    exact Real.sqrt_sq (by positivity)
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Real.sqrt_div (by positivity : (0:ℝ) ≤ n),
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ n), hs]
  field_simp

theorem sqrt_enclosure (a : UInt64) (ha : Finite a) (hx : 0 ≤ value a)
    (hf : Finite (Wasm.IEEE64.sqrt a)) :
    value (nextDown (Wasm.IEEE64.sqrt a)) ≤ Real.sqrt (value a) ∧
    Real.sqrt (value a) ≤ value (nextUp (Wasm.IEEE64.sqrt a)) := by
  by_cases hm : Wasm.IEEE64.scaledMagnitude a = 0
  · have hv : value a = 0 := by simp [value, Wasm.IEEE64.scaledValue, hm]
    have heq : Wasm.IEEE64.sqrt a = a := by
      simp [Wasm.IEEE64.sqrt, not_nan_of_finite ha, hm]
    rw [heq, hv, Real.sqrt_zero]
    simpa only [hv] using And.intro (nextDown_lt _ ha).le (nextUp_lt _ ha).le
  · have hsign : Wasm.IEEE64.sign a = false := by
      cases hs : Wasm.IEEE64.sign a
      · rfl
      · have hv : value a = -(Wasm.IEEE64.scaledMagnitude a:ℝ)/(2:ℝ)^1074 := by
          simp [value, Wasm.IEEE64.scaledValue, hs]
        have hp : (0:ℝ) < Wasm.IEEE64.scaledMagnitude a :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
        have hneg : value a < 0 := by rw [hv]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)
        exact False.elim (not_le_of_gt hneg hx)
    have heq := sqrt_positive_finite a ha hm hsign
    have hv : value a = (Wasm.IEEE64.scaledMagnitude a:ℝ)/(2:ℝ)^1074 := by
      simp [value, Wasm.IEEE64.scaledValue, hsign]
    rw [heq] at hf ⊢
    rw [hv, sqrt_scaled_value]
    exact sqrt_magnitude_enclosure _ hf

#print axioms sqrt_magnitude_enclosure
#print axioms sqrt_enclosure
end Project.ProofKit.F64Adjacent
