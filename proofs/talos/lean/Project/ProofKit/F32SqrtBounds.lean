import Project.ProofKit.F32RoundBounds
import Project.ProofKit.F32IntegerExact
import Project.ProofKit.F32Sqrt
import CodeLib.IEEE32.Rounders

namespace Project.ProofKit.F32SqrtBounds
open CodeLib.IEEE32

theorem roundSqrtMagnitude_spec (magnitude rootBound : Nat)
    (hLower : 24 ≤ rootBound) (hUpper : rootBound ≤ 274)
    (hbound : magnitude * 2 ^ 149 ≤ 2 ^ (2 * rootBound)) :
    Finite (Wasm.IEEE32.roundSqrtMagnitude magnitude) ∧
      Wasm.IEEE32.sign (Wasm.IEEE32.roundSqrtMagnitude magnitude) = false ∧
      |(Wasm.IEEE32.scaledMagnitude
            (Wasm.IEEE32.roundSqrtMagnitude magnitude) : ℝ) -
          Real.sqrt (magnitude * 2 ^ 149)| ≤ (2 : ℝ) ^ (rootBound - 23) := by
  by_cases hmagnitude : magnitude = 0
  · subst magnitude
    norm_num [Wasm.IEEE32.roundSqrtMagnitude, CodeLib.IEEE32.Finite,
      Wasm.IEEE32.isFinite, Wasm.IEEE32.sign,
      Wasm.IEEE32.scaledMagnitude, Wasm.IEEE32.exponent,
      Wasm.IEEE32.fraction, UInt32.toNat_ofNat]
  · let radicand := magnitude * 2 ^ 149
    let rootFloor := Nat.sqrt radicand
    let outputShift := Nat.log2 rootFloor - 23
    let rounded := Wasm.IEEE32.roundSqrtIntegral radicand outputShift
    let candidate := rounded * 2 ^ outputShift
    have hradicand : radicand ≤ 2 ^ (2 * rootBound) := hbound
    have hrootBound : rootFloor ≤ 2 ^ rootBound := by
      calc
        rootFloor ≤ Nat.sqrt (2 ^ (2 * rootBound)) := by
          simpa [rootFloor] using Nat.sqrt_le_sqrt hradicand
        _ = 2 ^ rootBound := by
          rw [show (2 : Nat) ^ (2 * rootBound) = ((2 : Nat) ^ rootBound) ^ 2 by
            rw [pow_two, ← pow_add, two_mul]]
          exact Nat.sqrt_eq' _
    have hradicandNe : radicand ≠ 0 := by
      simp [radicand, hmagnitude]
    have hrootNe : rootFloor ≠ 0 := by
      intro h
      have hupper := Nat.lt_succ_sqrt' radicand
      simp [rootFloor, h] at hupper
      apply hradicandNe
      omega
    have hrootLt : rootFloor < 2 ^ (rootBound + 1) :=
      hrootBound.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    have hlogUpper : Nat.log2 rootFloor < rootBound + 1 :=
      (Nat.log2_lt hrootNe).2 hrootLt
    have hshiftMax : outputShift ≤ rootBound - 23 := by
      simp [outputShift]
      omega
    have hroundBounds := roundSqrtIntegral_bounds radicand outputShift
    change rootFloor / 2 ^ outputShift ≤ rounded ∧
      rounded ≤ rootFloor / 2 ^ outputShift + 1 at hroundBounds
    have hrepresentable : roundedMagnitude candidate = candidate := by
      by_cases hzero : outputShift = 0
      · have hlog : Nat.log2 rootFloor ≤ 23 := by
          simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
        have hrootLt24 : rootFloor < 2 ^ 24 := by
          have hself : rootFloor < 2 ^ (Nat.log2 rootFloor + 1) :=
            Nat.lt_log2_self
          exact hself.trans_le
            (Nat.pow_le_pow_right (by omega) (by omega))
        have hroundedUpper : rounded ≤ 2 ^ 24 := by
          simp [hzero] at hroundBounds
          omega
        simp [candidate, hzero, roundedMagnitude_eq_self hroundedUpper]
      · have hshiftPos : 0 < outputShift := Nat.pos_of_ne_zero hzero
        have hshiftEq : 23 + outputShift = Nat.log2 rootFloor := by
          simp [outputShift]
          omega
        have hpowLower : 2 ^ 23 * 2 ^ outputShift ≤ rootFloor := by
          rw [← pow_add, hshiftEq]
          exact Nat.log2_self_le hrootNe
        have hpowUpper : rootFloor < 2 ^ 24 * 2 ^ outputShift := by
          rw [← pow_add]
          have heq : 24 + outputShift = Nat.log2 rootFloor + 1 := by
            rw [← hshiftEq]
            omega
          rw [heq]
          exact Nat.lt_log2_self
        have hquotientLower :
            2 ^ 23 ≤ rootFloor / 2 ^ outputShift :=
          (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
        have hquotientUpper :
            rootFloor / 2 ^ outputShift < 2 ^ 24 :=
          (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
        exact F32IntegerExact.roundedMagnitude_mul_power_le rounded outputShift (by omega)
    have hcandidateMax : candidate < 2 ^ (rootBound + 2) := by
      by_cases hzero : outputShift = 0
      · have hlog : Nat.log2 rootFloor ≤ 23 := by
          simpa [outputShift, Nat.sub_eq_zero_iff_le] using hzero
        have hrootLt24 : rootFloor < 2 ^ 24 := by
          exact Nat.lt_log2_self.trans_le
            (Nat.pow_le_pow_right (by omega) (by omega))
        have hroundedUpper : rounded ≤ 2 ^ 24 := by
          simp [hzero] at hroundBounds
          omega
        simp [candidate, hzero]
        exact hroundedUpper.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
      · have hroundedUpper : rounded ≤ 2 ^ 24 := by
          have hshiftPos : 0 < outputShift := Nat.pos_of_ne_zero hzero
          have hshiftEq : 23 + outputShift = Nat.log2 rootFloor := by
            simp [outputShift]
            omega
          have hpowUpper : rootFloor < 2 ^ 24 * 2 ^ outputShift := by
            rw [← pow_add]
            have heq : 24 + outputShift = Nat.log2 rootFloor + 1 := by
              rw [← hshiftEq]
              omega
            rw [heq]
            exact Nat.lt_log2_self
          have hquotientUpper :
              rootFloor / 2 ^ outputShift < 2 ^ 24 :=
            (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
          omega
        calc
          candidate ≤ 2 ^ 24 * 2 ^ (rootBound - 23) :=
            Nat.mul_le_mul hroundedUpper
              (Nat.pow_le_pow_right (by omega) hshiftMax)
          _ = 2 ^ (rootBound + 1) := by rw [← pow_add]; congr 1; omega
          _ < 2 ^ (rootBound + 2) := Nat.pow_lt_pow_right (by omega) (by omega)
    have hpack := F32RoundBounds.roundScaledMagnitude_spec false candidate (rootBound + 2) (by omega) hcandidateMax
    have hsign := F32RoundBounds.sign_roundScaledMagnitude false candidate (rootBound + 2) (by omega) hcandidateMax
    have hactual : Wasm.IEEE32.roundSqrtMagnitude magnitude =
        Wasm.IEEE32.roundScaledMagnitude false candidate := by
      simp only [Wasm.IEEE32.roundSqrtMagnitude, beq_iff_eq,
        if_neg hmagnitude]
      rfl
    have herrHalf := roundSqrtIntegral_real_error radicand outputShift
    have hhalf : (2 : ℝ) ^ outputShift / 2 ≤ (2 : ℝ) ^ (rootBound - 23) := by
      calc
        (2 : ℝ) ^ outputShift / 2 ≤ (2 : ℝ) ^ outputShift := by
          have hp : 0 ≤ (2 : ℝ) ^ outputShift := by positivity
          linarith
        _ ≤ (2 : ℝ) ^ (rootBound - 23) :=
          pow_le_pow_right₀ (by norm_num) hshiftMax
    have herr : |(candidate : ℝ) - Real.sqrt radicand| ≤
        (2 : ℝ) ^ (rootBound - 23) := by
      have := herrHalf.trans hhalf
      simpa only [candidate, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        using this
    rw [hactual]
    refine ⟨hpack.1, hsign, ?_⟩
    rw [hpack.2.1, hrepresentable]
    simpa only [radicand, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      using herr

noncomputable def epsilon (rootBound : Nat) : ℝ := (2 : ℝ) ^ (rootBound - 23) / 2 ^ 149

theorem sqrt_real_error (a : UInt32) (rootBound : Nat)
    (hLower : 24 ≤ rootBound) (hUpper : rootBound ≤ 274)
    (ha : CodeLib.IEEE32.Finite a) (hSign : Wasm.IEEE32.sign a = false)
    (hRange : Wasm.IEEE32.scaledMagnitude a * 2 ^ 149 ≤ 2 ^ (2 * rootBound)) :
    CodeLib.IEEE32.Finite (LeanExe.Float32.sqrtBits a) ∧
      |value (LeanExe.Float32.sqrtBits a) - Real.sqrt (value a)| ≤ epsilon rootBound := by
  rw [F32Sqrt.sqrt_eq]
  have hNa := not_nan_of_finite ha
  have hInf := not_infinite_of_finite ha
  by_cases hZero : Wasm.IEEE32.scaledMagnitude a = 0
  · have hValue : value a = 0 := by simp [value, Wasm.IEEE32.scaledValue, hZero]
    simp only [Wasm.IEEE32.sqrt, hNa, Bool.false_eq_true, ite_false, beq_iff_eq, hZero, ite_true]
    refine ⟨ha, ?_⟩
    rw [hValue, Real.sqrt_zero, sub_self, abs_zero]
    unfold epsilon
    positivity
  · have hOutput := roundSqrtMagnitude_spec (Wasm.IEEE32.scaledMagnitude a) rootBound hLower hUpper hRange
    have hRoot : Real.sqrt ((Wasm.IEEE32.scaledMagnitude a : ℝ) * 2 ^ 149) / 2 ^ 149 =
        Real.sqrt (value a) := by
      calc
        Real.sqrt ((Wasm.IEEE32.scaledMagnitude a : ℝ) * 2 ^ 149) / 2 ^ 149 =
            Real.sqrt (((Wasm.IEEE32.scaledMagnitude a : ℝ) * 2 ^ 149) / ((2 : ℝ) ^ 149) ^ 2) := by
          rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
        _ = Real.sqrt (value a) := by
          congr 1
          simp only [value, Wasm.IEEE32.scaledValue, hSign, Bool.false_eq_true, ite_false]
          push_cast
          field_simp
    simp only [Wasm.IEEE32.sqrt, hNa, Bool.false_eq_true, ite_false, beq_iff_eq, hZero, hInf, hSign]
    refine ⟨hOutput.1, ?_⟩
    rw [← hRoot]
    simp only [value, Wasm.IEEE32.scaledValue, hOutput.2.1, Bool.false_eq_true, ite_false]
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 149)]
    simpa only [Int.cast_natCast, epsilon] using div_le_div_of_nonneg_right hOutput.2.2
      (by positivity : (0 : ℝ) ≤ 2 ^ 149)

#print axioms roundSqrtMagnitude_spec
#print axioms sqrt_real_error
end Project.ProofKit.F32SqrtBounds
