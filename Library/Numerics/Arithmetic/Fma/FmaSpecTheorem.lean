import Library.Numerics.Arithmetic.Fma.FmaTheorem
import Library.Numerics.Arithmetic.Fma.FmaSpec

/-!
`FmaSpec.FmaNearest`, the form of the fused multiply-add that the proofs of `erfc`, `tgamma`, and
`lgamma` use, as a corollary of `FmaTheorem.fma_toBits`.  For finite operands with
`|a · b + c| ≤ 2 ^ 1023` the reference is a zero for an exact zero sum and otherwise the
nearest-even word of `a · b + c` below the overflow threshold, which is finite and no farther from
`a · b + c` than any finite word.  A word of the opposite sign is no closer than zero.
-/

namespace Library.Numerics.Arithmetic.Fma.FmaSpecTheorem
open Library.Numerics.Arithmetic.Fma FmaTheorem CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative

set_option exponentiation.threshold 4096

theorem value_nonneg_of_sign (v : UInt64) (hs : Wasm.IEEE64.sign v = false) : 0 ≤ value v := by
  rw [F64Exact.value_of_sign v hs]
  positivity

theorem value_nonpos_of_sign (v : UInt64) (hs : Wasm.IEEE64.sign v = true) : value v ≤ 0 := by
  unfold value Wasm.IEEE64.scaledValue
  simp only [hs, ite_true, Int.cast_neg, Int.cast_natCast, neg_div]
  have : (0 : ℝ) ≤ (Wasm.IEEE64.scaledMagnitude v : ℝ) / 2 ^ 1074 := by positivity
  linarith

theorem negate_sign (v : UInt64) (hs : Wasm.IEEE64.sign v = true) :
    Wasm.IEEE64.sign (Wasm.IEEE64.negate v) = false := by
  have h := F64SignedRounding.negate_toNat v
  rw [hs, ite_eq_left rfl] at h
  have hv := v.toNat_lt
  unfold Wasm.IEEE64.sign at hs ⊢
  rw [h]
  simp only [decide_eq_true_eq] at hs
  simp only [decide_eq_false_iff_not, not_le]
  simp only [Nat.reducePow] at *
  omega

theorem threshold_above (t : ℝ) (ht : t ≤ 2 ^ 1023) : t < F64PositiveRounding.overflowThreshold := by
  have : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - 2 ^ 970 := rfl
  rw [this]
  have : (2 : ℝ) ^ 1023 < 2 ^ 1024 - 2 ^ 970 := by norm_num
  linarith

/-- The nearest-even word of `0 < t ≤ 2 ^ 1023` is finite and nearest among all finite words. -/
theorem nearest_pos (t : ℝ) (ht0 : 0 < t) (ht : t ≤ 2 ^ 1023) :
    Finite (F64SignedRounding.roundNearestEven t) ∧
      ∀ v : UInt64, Finite v →
        |value (F64SignedRounding.roundNearestEven t) - t| ≤ |value v - t| := by
  have hr : F64SignedRounding.roundNearestEven t = F64NearestEven.roundNearestEven t := by
    unfold F64SignedRounding.roundNearestEven
    rw [ite_eq_left ht0.le, F64PositiveRounding.reference_finite _ (threshold_above t ht)]
  rw [hr]
  have hn := (F64NearestEven.roundNearestEven_spec t).1
  obtain ⟨hwf, _⟩ := nearest_finite t _ hn
  refine ⟨hwf, fun v hv => ?_⟩
  cases hs : Wasm.IEEE64.sign v
  · exact hn.2 v (F64Magnitude.lt_limit_of_finite v hv hs)
  · have h0 := hn.2 0 (by decide)
    rw [F64Magnitude.value_zero, zero_sub, abs_neg, abs_of_pos ht0] at h0
    have hv0 := value_nonpos_of_sign v hs
    rw [abs_of_neg (by linarith : value v - t < 0)]
    linarith

/-- The nearest-even word of `-2 ^ 1023 ≤ t < 0` is finite and nearest among all finite words. -/
theorem nearest_neg (t : ℝ) (ht0 : t < 0) (ht : -t ≤ 2 ^ 1023) :
    Finite (F64SignedRounding.roundNearestEven t) ∧
      ∀ v : UInt64, Finite v →
        |value (F64SignedRounding.roundNearestEven t) - t| ≤ |value v - t| := by
  have hr : F64SignedRounding.roundNearestEven t =
      Wasm.IEEE64.negate (F64NearestEven.roundNearestEven (-t)) := by
    unfold F64SignedRounding.roundNearestEven
    rw [ite_eq_right (not_le.mpr ht0),
      F64PositiveRounding.reference_finite _ (threshold_above (-t) ht)]
  rw [hr]
  have hn := (F64NearestEven.roundNearestEven_spec (-t)).1
  obtain ⟨hwf, _⟩ := nearest_finite (-t) _ hn
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value _ hwf
  refine ⟨hnf, fun v hv => ?_⟩
  rw [hnv, show -value (F64NearestEven.roundNearestEven (-t)) - t =
    -(value (F64NearestEven.roundNearestEven (-t)) - -t) by ring, abs_neg]
  cases hs : Wasm.IEEE64.sign v
  · have h0 := hn.2 0 (by decide)
    rw [F64Magnitude.value_zero, zero_sub, neg_neg, abs_of_neg ht0] at h0
    have hv0 := value_nonneg_of_sign v hs
    rw [abs_of_pos (by linarith : 0 < value v - t)]
    linarith
  · obtain ⟨hvf, hvv⟩ := F64Magnitude.negate_value v hv
    have h1 := hn.2 (Wasm.IEEE64.negate v)
      (F64Magnitude.lt_limit_of_finite _ hvf (negate_sign v hs))
    rw [hvv, show -value v - -t = -(value v - t) by ring, abs_neg] at h1
    exact h1

theorem zero_word (b : Bool) : Finite (Wasm.IEEE64.signMask b) ∧
    value (Wasm.IEEE64.signMask b) = 0 := by
  cases b
  · refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
    exact F64Magnitude.value_zero
  · refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
    have h : Wasm.IEEE64.scaledValue (Wasm.IEEE64.signMask true) = 0 := by decide +kernel
    rw [value, h, Int.cast_zero, zero_div]

/-- For finite operands with `|a · b + c| ≤ 2 ^ 1023`, `Fma.fma` returns a finite word nearest to
`a · b + c`. -/
theorem fma_nearest : FmaSpec.FmaNearest := by
  intro a b c ha hb hc ht
  rw [fma_toBits]
  unfold fmaReference
  rw [not_nan_of_finite ha, not_nan_of_finite hb, not_nan_of_finite hc,
    ite_eq_right (by decide)]
  dsimp only
  rw [not_infinite_of_finite ha, not_infinite_of_finite hb, not_infinite_of_finite hc,
    ite_eq_right (by decide), ite_eq_right (by decide)]
  by_cases ht0 : value a.toBits * value b.toBits + value c.toBits = 0
  · rw [ite_eq_left ht0, ht0]
    have hz : ∀ w : UInt64, Finite w ∧ value w = 0 →
        Finite w ∧ ∀ v : UInt64, Finite v → |value w - 0| ≤ |value v - 0| := by
      intro w hw
      refine ⟨hw.1, fun v _ => ?_⟩
      rw [hw.2, sub_zero, abs_zero]
      exact abs_nonneg _
    split_ifs
    · exact hz _ (zero_word _)
    · exact hz 0 (zero_word false)
  · rw [ite_eq_right ht0]
    obtain ⟨h1, h2⟩ := abs_le.mp ht
    rcases lt_or_gt_of_ne ht0 with hneg | hpos
    · exact nearest_neg _ hneg (by linarith)
    · exact nearest_pos _ hpos h2

#print axioms nearest_pos
#print axioms nearest_neg
#print axioms fma_nearest

end Library.Numerics.Arithmetic.Fma.FmaSpecTheorem
