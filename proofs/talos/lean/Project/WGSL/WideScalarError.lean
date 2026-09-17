import Project.WGSL.FusedError
import Project.ProofKit.F32DyadicReal

namespace Project.WGSL.Binary32
open CodeLib.IEEE32 Project.ProofKit LeanExe.WGSL

set_option exponentiation.threshold 512

theorem signed_zero_value (negative : Bool) :
    Finite (Wasm.IEEE32.signMask negative) ∧ value (Wasm.IEEE32.signMask negative) = 0 := by
  have hs := F32DyadicBounds.dyadic_zero negative 149
  simp only [Wasm.IEEE32.roundDyadicMagnitude, beq_self_eq_true, ite_true] at hs
  refine ⟨hs.1, ?_⟩
  simp only [value, Wasm.IEEE32.scaledValue, hs.2.2]
  split <;> norm_num

theorem signed_numerator (z : Int) :
    F32DyadicReal.exactValue (z < 0) z.natAbs 149 = (z:ℝ) / 2^298 := by
  simp only [F32DyadicReal.exactValue, decide_eq_true_eq]
  have hz (z : Int) : (if z < 0 then -(z.natAbs:ℝ) else z.natAbs) = (z:ℝ) := by
    by_cases hn : z < 0
    · rw [if_pos hn, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg hn]
      push_cast
      ring
    · rw [if_neg hn, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonneg (by omega)]
  rw [hz]

theorem fused_exact_value (a b c : UInt32) :
    F32DyadicReal.exactValue (fusedNumerator a b c < 0) (fusedNumerator a b c).natAbs 149 =
      value a * value b + value c := by
  rw [signed_numerator]
  simp [value, fusedNumerator]
  ring

theorem fma_real_wide (a b c : UInt32) (ha : Finite a) (hb : Finite b) (hc : Finite c)
    (hbound : |value a * value b + value c| < (2:ℝ)^127) :
    Finite (fma a b c) ∧
    |value (fma a b c) - (value a * value b + value c)| ≤
      F32AddBounds.unitRoundoff * |value a * value b + value c| + F32MulBounds.multiplicationUnderflowEpsilon := by
  have hmax : (fusedNumerator a b c).natAbs < 2^425 := by
    rw [← fused_exact_value, F32DyadicReal.exact_abs] at hbound
    have h := (div_lt_iff₀ (by positivity : (0:ℝ) < 2^(149+149))).mp hbound
    rw [← pow_add] at h
    exact_mod_cast h
  by_cases hz : fusedNumerator a b c = 0
  · have heq : value a * value b + value c = 0 := by
      rw [← fused_exact_value, hz]
      norm_num [F32DyadicReal.exactValue]
    have hs := signed_zero_value ((Wasm.IEEE32.sign a != Wasm.IEEE32.sign b) && Wasm.IEEE32.sign c)
    simp only [fma, not_nan_of_finite ha, not_nan_of_finite hb, not_nan_of_finite hc,
      not_infinite_of_finite ha, not_infinite_of_finite hb, not_infinite_of_finite hc,
      Bool.or_false, Bool.false_or, Bool.false_eq_true, ite_false, hz, beq_self_eq_true, ite_true]
    refine ⟨hs.1, ?_⟩
    rw [hs.2, heq]
    norm_num [F32MulBounds.multiplicationUnderflowEpsilon]
  · have hs := F32DyadicReal.real_mixed (fusedNumerator a b c < 0)
      (fusedNumerator a b c).natAbs 149 (by decide) hmax
    rw [fused_exact_value] at hs
    simpa [fma, not_nan_of_finite ha, not_nan_of_finite hb, not_nan_of_finite hc,
      not_infinite_of_finite ha, not_infinite_of_finite hb, not_infinite_of_finite hc, hz] using hs

noncomputable def stepError (accBudget productBudget : ℝ) : ℝ :=
  let u := F32AddBounds.unitRoundoff
  let eta := F32MulBounds.multiplicationUnderflowEpsilon
  u * (accBudget + 2 * productBudget + u * productBudget + eta) + eta

theorem stepError_nonneg {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) : 0 ≤ stepError c p := by
  unfold stepError F32AddBounds.unitRoundoff F32MulBounds.multiplicationUnderflowEpsilon
  positivity

theorem accumulation_error_wide {p : Profile} {acc a b result : UInt32} {cBudget pBudget : ℝ}
    (hc : Finite acc) (ha : Finite a) (hb : Finite b)
    (hc0 : 0 ≤ cBudget) (hp0 : 0 ≤ pBudget)
    (hcBound : |value acc| ≤ cBudget) (hpBound : |value a * value b| ≤ pBudget)
    (hRange : cBudget + pBudget + F32AddBounds.unitRoundoff * pBudget +
      F32MulBounds.multiplicationUnderflowEpsilon < (2:ℝ)^127)
    (update : Accumulate semantics p acc a b result) :
    Finite result ∧ |value result - (value acc + value a * value b)| ≤ stepError cBudget pBudget := by
  have hu : 0 ≤ F32AddBounds.unitRoundoff := by norm_num [F32AddBounds.unitRoundoff]
  have he : 0 ≤ F32MulBounds.multiplicationUnderflowEpsilon := by
    norm_num [F32MulBounds.multiplicationUnderflowEpsilon]
  have hup := mul_nonneg hu hp0
  cases update with
  | @separate product result cm ca _ _ _ mul add =>
      have hm : product = Wasm.IEEE32.mul a b := mul.2
      have hr : result = Wasm.IEEE32.add acc product := add.2
      subst product; subst result
      have hm := F32MulBounds.mul_real_mixed a b ha hb (by linarith)
      have hmError : |value (Wasm.IEEE32.mul a b) - value a * value b| ≤
          F32AddBounds.unitRoundoff * pBudget + F32MulBounds.multiplicationUnderflowEpsilon :=
        by
          have h := mul_le_mul_of_nonneg_left hpBound hu
          linarith [hm.2]
      have hmMag : |value (Wasm.IEEE32.mul a b)| ≤
          pBudget + F32AddBounds.unitRoundoff * pBudget + F32MulBounds.multiplicationUnderflowEpsilon := by
        have ht := abs_sub_le (value (Wasm.IEEE32.mul a b)) (value a * value b) 0
        simp only [sub_zero] at ht
        linarith
      have hsum := abs_add_le (value acc) (value (Wasm.IEEE32.mul a b))
      have hadd := F32AddBounds.add_real_relative acc (Wasm.IEEE32.mul a b) hc hm.1 (by linarith)
      have heq : value (Wasm.IEEE32.add acc (Wasm.IEEE32.mul a b)) - (value acc + value a * value b) =
          (value (Wasm.IEEE32.add acc (Wasm.IEEE32.mul a b)) - (value acc + value (Wasm.IEEE32.mul a b))) +
          (value (Wasm.IEEE32.mul a b) - value a * value b) := by ring
      refine ⟨hadd.1, ?_⟩
      rw [heq]
      have ht := abs_add_le
        (value (Wasm.IEEE32.add acc (Wasm.IEEE32.mul a b)) - (value acc + value (Wasm.IEEE32.mul a b)))
        (value (Wasm.IEEE32.mul a b) - value a * value b)
      unfold stepError
      nlinarith [hadd.2]
  | fused _ _ op =>
      have hr : result = fma a b acc := op.2
      subst result
      have hsum := abs_add_le (value a * value b) (value acc)
      have hf := fma_real_wide a b acc ha hb hc (by linarith)
      refine ⟨hf.1, ?_⟩
      rw [add_comm (value acc)]
      unfold stepError
      nlinarith [hf.2]

#print axioms fma_real_wide
#print axioms accumulation_error_wide
end Project.WGSL.Binary32
