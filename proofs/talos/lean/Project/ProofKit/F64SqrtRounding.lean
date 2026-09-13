import Project.ProofKit.F64DyadicBounds

namespace Project.ProofKit.F64SqrtRounding
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem sqrt_relative (magnitude : Nat) (hm : magnitude ≠ 0) (hmax : magnitude < 2^2098) :
    Finite (Wasm.IEEE64.roundSqrtMagnitude magnitude) ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundSqrtMagnitude magnitude) = false ∧
    |(Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundSqrtMagnitude magnitude) : ℝ) -
      Real.sqrt (magnitude * 2^1074 : Nat)| ≤
      unitRoundoff64 * Real.sqrt (magnitude * 2^1074 : Nat) := by
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
  have hshift : 0 < outputShift := by dsimp [outputShift]; omega
  have hshiftMax : outputShift ≤ 1533 := by dsimp [outputShift]; omega
  have hshiftEq : 52 + outputShift = Nat.log2 rootFloor := by dsimp [outputShift]; omega
  have hpowLower : 2^52 * 2^outputShift ≤ rootFloor := by
    rw [← pow_add, hshiftEq]
    exact Nat.log2_self_le hrootNe
  have hpowUpper : rootFloor < 2^53 * 2^outputShift := by
    rw [← pow_add, show 53 + outputShift = Nat.log2 rootFloor + 1 by omega]
    exact Nat.lt_log2_self
  have hquotLower : 2^52 ≤ rootFloor / 2^outputShift :=
    (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : rootFloor / 2^outputShift < 2^53 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hroundBounds := CodeLib.IEEE32.roundSqrtIntegral_bounds radicand outputShift
  change rootFloor / 2^outputShift ≤ rounded ∧ rounded ≤ rootFloor / 2^outputShift + 1
    at hroundBounds
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
  have hpack := F64Packing.pack_spec false candidate hcandidateMax
  have hactual : Wasm.IEEE64.roundSqrtMagnitude magnitude =
      Wasm.IEEE64.roundScaledMagnitude false candidate := by
    simp only [Wasm.IEEE64.roundSqrtMagnitude, beq_iff_eq, if_neg hm]
    rfl
  have herr := CodeLib.IEEE32.roundSqrtIntegral_real_error radicand outputShift
  have hrootReal : (2 : ℝ)^52 * (2 : ℝ)^outputShift ≤ Real.sqrt radicand := by
    calc
      (2 : ℝ)^52 * (2 : ℝ)^outputShift ≤ rootFloor := by exact_mod_cast hpowLower
      _ ≤ Real.sqrt radicand := Real.nat_sqrt_le_real_sqrt
  have hhalf : (2 : ℝ)^outputShift / 2 ≤ unitRoundoff64 * Real.sqrt radicand := by
    calc
      (2 : ℝ)^outputShift / 2 = unitRoundoff64 * ((2 : ℝ)^52 * (2 : ℝ)^outputShift) := by
        norm_num [unitRoundoff64]
        ring
      _ ≤ unitRoundoff64 * Real.sqrt radicand :=
        mul_le_mul_of_nonneg_left hrootReal (by norm_num [unitRoundoff64])
  rw [hactual]
  refine ⟨hpack.1, hpack.2.2, ?_⟩
  rw [hpack.2.1, hrepresentable]
  simpa only [candidate, rounded, radicand, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    using herr.trans hhalf

#print axioms sqrt_relative
end Project.ProofKit.F64SqrtRounding
