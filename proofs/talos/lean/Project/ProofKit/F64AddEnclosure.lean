import Project.ProofKit.F64Enclosure

namespace Project.ProofKit.F64Adjacent
open CodeLib.IEEE64
open Project.ProofKit.F64Packing
set_option exponentiation.threshold 4096

theorem pack_enclosure (negative : Bool) (n : Nat)
    (hf : Finite (Wasm.IEEE64.roundScaledMagnitude negative n)) :
    let exactValue := (if negative then -(n:ℝ) else n)/(2:ℝ)^1074
    value (nextDown (Wasm.IEEE64.roundScaledMagnitude negative n)) ≤ exactValue ∧
    exactValue ≤ value (nextUp (Wasm.IEEE64.roundScaledMagnitude negative n)) := by
  have hp := pack_finite_spec negative n hf
  have hn : Nat.log2 n-52 = 0 ∨
      2^52*2^(Nat.log2 n-52) ≤
        Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundScaledMagnitude negative n) := by
    by_cases hsmall : n < 2^53
    · left
      by_cases hz : n = 0
      · simp [hz]
      · have hl := (Nat.log2_lt hz).mpr hsmall
        omega
    · right
      rw [hp.1]
      exact roundedMagnitude_lower n (by omega)
  simpa only [hp.2] using enclosure_of_magnitude
    (Wasm.IEEE64.roundScaledMagnitude negative n) (Nat.log2 n-52) n hf
    (by positivity) hn (pack_magnitude_error negative n hf)

theorem signed_pack_enclosure (z : Int)
    (hf : Finite (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs)) :
    value (nextDown (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs)) ≤
      (z:ℝ)/(2:ℝ)^1074 ∧
    (z:ℝ)/(2:ℝ)^1074 ≤
      value (nextUp (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs)) := by
  have hz : (if decide (z < 0) then -(z.natAbs:ℝ) else z.natAbs) = (z:ℝ) := by
    by_cases hn : z < 0
    · simp only [hn, decide_true, ite_true, Nat.cast_natAbs, abs_of_neg hn, Int.cast_neg,
        neg_neg]
    · simp only [hn, decide_false, Bool.false_eq_true, ite_false, Nat.cast_natAbs,
        abs_of_nonneg (le_of_not_gt hn)]
  simpa only [hz] using pack_enclosure (z < 0) z.natAbs hf

theorem add_enclosure (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hf : Finite (Wasm.IEEE64.add a b)) :
    value (nextDown (Wasm.IEEE64.add a b)) ≤ value a+value b ∧
    value a+value b ≤ value (nextUp (Wasm.IEEE64.add a b)) := by
  let z := Wasm.IEEE64.scaledValue a+Wasm.IEEE64.scaledValue b
  have hzval : value a+value b = (z:ℝ)/(2:ℝ)^1074 := by
    simp only [value, z, Int.cast_add, add_div]
  rw [hzval]
  by_cases hz : z = 0
  · have hzero : Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) = 0 := by
      simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
        not_infinite_of_finite ha, not_infinite_of_finite hb, z, hz]
      split <;> decide +kernel
    have hv : value (Wasm.IEEE64.add a b) = 0 := by simp [value, hzero]
    simpa only [hz, Int.cast_zero, zero_div, hv] using
      And.intro (nextDown_lt _ hf).le (nextUp_lt _ hf).le
  · have heq : Wasm.IEEE64.add a b =
        Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs := by
      simp [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
        not_infinite_of_finite ha, not_infinite_of_finite hb, z, hz]
    rw [heq] at hf ⊢
    exact signed_pack_enclosure z hf

theorem sub_enclosure (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hf : Finite (Wasm.IEEE64.sub a b)) :
    value (nextDown (Wasm.IEEE64.sub a b)) ≤ value a-value b ∧
    value a-value b ≤ value (nextUp (Wasm.IEEE64.sub a b)) := by
  have hn := negate_spec b hb
  have hv : value (Wasm.IEEE64.negate b) = -value b := by
    simp [value, hn.2]
    ring
  simpa only [Wasm.IEEE64.sub, hv, ← sub_eq_add_neg] using
    add_enclosure a (Wasm.IEEE64.negate b) ha hn.1 hf

#print axioms pack_enclosure
#print axioms signed_pack_enclosure
#print axioms add_enclosure
#print axioms sub_enclosure
end Project.ProofKit.F64Adjacent
