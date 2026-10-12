import LeanExe.ProofKit.F64Approx

/-!
A function that returns its argument near a fixed point.  When the exact result `y` lies within the
fraction `ρ ≤ 2 ^ -53` of the argument's value, the argument's word is within one representable
step of the nearest-even reference of `y`: zeros give zero, normal arguments from binade 2 on use
`F64Approx.within_one_rel`, and the smallest arguments have an error below one subnormal spacing.
-/

namespace LeanExe.ProofKit.F64WithinSelf
open CodeLib.IEEE64 F64Approx

set_option exponentiation.threshold 4096

/-- A word whose value is zero is within one step of the reference of zero. -/
theorem within_zero_word (x : UInt64) (hx : value x = 0) :
    F64SignedRounding.WithinSteps 1 0 x := by
  have hm : Wasm.IEEE64.scaledMagnitude x = 0 := by
    have h := hx
    simp only [value, div_eq_zero_iff, Int.cast_eq_zero] at h
    rcases h with h | h
    · have := natAbs_scaledValue x
      rw [h] at this
      simpa using this.symm
    · exfalso
      norm_num at h
  have hlt := x.toNat_lt
  have hmod : x.toNat % 2 ^ 63 = 0 := by
    simp only [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at hm
    by_cases hc : (x.toNat / 2 ^ 52 % 2 ^ 11 == 0) = true
    · simp only [hc, ↓reduceIte] at hm
      rw [beq_iff_eq] at hc
      omega
    · simp only [hc, ↓reduceIte, Bool.false_eq_true] at hm
      exfalso
      have : 0 < (2 ^ 52 + x.toNat % 2 ^ 52) * 2 ^ (x.toNat / 2 ^ 52 % 2 ^ 11 - 1) := by
        positivity
      omega
  have hpos : F64SignedRounding.position x = 0 := by
    unfold F64SignedRounding.position Wasm.IEEE64.sign
    split <;> rename_i h <;> simp at h <;> omega
  have hr : F64SignedRounding.position (F64SignedRounding.roundNearestEven 0) = 0 := by
    simp only [F64SignedRounding.roundNearestEven, le_refl, ite_true,
      F64SignedRounding.positive_reference_zero]
    rfl
  refine ⟨by omega, ?_⟩
  rw [hpos, hr]
  norm_num

theorem within_self_pos (x : UInt64) (hxf : Finite x) (y ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / 2 ^ 53) (hx0 : 0 < value x) (h : |value x - y| ≤ ρ * value x) :
    F64SignedRounding.WithinSteps 1 y x := by
  have hyl : (1 - ρ) * value x ≤ y := by
    have := (abs_le.mp h).2
    linarith
  rcases Nat.lt_or_ge (Wasm.IEEE64.exponent x) 2 with he | he
  · -- below binade 2: an error below one subnormal spacing
    have hB0 : value (UInt64.ofNat (0 * 2 ^ 52)) = 0 := F64Magnitude.value_zero_boundary
    have hX : value x < 1 / 2 ^ 1021 := by
      have h := F64Magnitude.magnitude_lt x 2 (-1021) (by norm_num) (by norm_num) he
      rw [abs_of_pos hx0] at h
      have h2 : (2 : ℝ) ^ (-1021 : ℤ) = 1 / 2 ^ 1021 := by norm_num
      exact h.trans_le (le_of_eq h2)
    refine within_one_of_error y x 0 (by norm_num) (ρ * value x) hxf h ?_ ?_ ?_
    · rw [hB0, zero_add]
      nlinarith
    · have : ρ * value x ≤ 1 / 2 ^ 53 * (1 / 2 ^ 1021) := by
        apply mul_le_mul hρ hX.le hx0.le (by positivity)
      norm_num at this ⊢
      linarith
    · nlinarith
  · have hb := binade_bounds x hxf (by omega)
    rw [abs_of_pos hx0] at hb
    exact within_one_rel y x (value x) (Wasm.IEEE64.exponent x) he
      (by have := hxf; simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne,
        ne_eq] at this; have : Wasm.IEEE64.exponent x < 2048 := Nat.mod_lt _ (by norm_num); omega)
      hb.1 hb.2 ρ ρ hρ0 hρ0 hxf h hyl (by nlinarith) (by nlinarith)

/-- The argument's word is within one step of the reference of `y` when `y` lies within the
fraction `ρ ≤ 2 ^ -53` of the argument's value. -/
theorem within_one_of_self (x : UInt64) (hxf : Finite x) (y ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / 2 ^ 53) (h : |value x - y| ≤ ρ * |value x|) :
    F64SignedRounding.WithinSteps 1 y x := by
  rcases lt_trichotomy (value x) 0 with hn | hz | hp
  · have hnv := F64Magnitude.negate_value x hxf
    apply within_of_negate
    apply within_self_pos _ hnv.1 (-y) ρ hρ0 hρ (by rw [hnv.2]; linarith)
    rw [hnv.2, show -value x - -y = -(value x - y) by ring, abs_neg]
    rw [abs_of_neg hn] at h
    exact h
  · have hy : y = 0 := by
      rw [hz, abs_zero, mul_zero, zero_sub, abs_neg] at h
      exact abs_nonpos_iff.mp h
    rw [hy]
    exact within_zero_word x hz
  · rw [abs_of_pos hp] at h
    exact within_self_pos x hxf y ρ hρ0 hρ hp h

#print axioms within_zero_word
#print axioms within_one_of_self

/-- `within_one_rel` for either sign of `y`. -/
theorem rel_finish (c : UInt64) (hcf : Finite c) (y X : ℝ) (n : ℕ) (hn2 : 2 ≤ n) (hn : n < 2047)
    (hX : value (UInt64.ofNat (n * 2 ^ 52)) ≤ X)
    (hX2 : X < 2 * value (UInt64.ofNat (n * 2 ^ 52))) (κ ρ : ℝ) (hκ0 : 0 ≤ κ) (hρ0 : 0 ≤ ρ)
    (hc : |value c - y| ≤ ρ * X) (hyl : (1 - κ) * X ≤ |y|)
    (hρ : ρ ≤ 3 / 2 / 2 ^ 53 * (1 - κ - ρ)) (hκ : κ + ρ < 1 / 3) :
    F64SignedRounding.WithinSteps 1 y c := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy] at hyl
    exact within_one_rel y c X n hn2 hn hX hX2 κ ρ hκ0 hρ0 hcf hc hyl hρ hκ
  · rw [abs_of_neg hy] at hyl
    have hnv := F64Magnitude.negate_value c hcf
    apply within_of_negate
    refine within_one_rel (-y) _ X n hn2 hn hX hX2 κ ρ hκ0 hρ0 hnv.1 ?_ hyl hρ hκ
    rw [hnv.2, show -value c - -y = -(value c - y) by ring, abs_neg]
    exact hc

/-- `within_one_of_error` for either sign of `y`. -/
theorem abs_finish (c : UInt64) (hcf : Finite c) (y E : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2047)
    (hc : |value c - y| ≤ E) (hy : value (UInt64.ofNat (n * 2 ^ 52)) + E ≤ |y|)
    (hE : E < 3 * ((2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ 1074) / 2) :
    F64SignedRounding.WithinSteps 1 y c := by
  have hB := F64PositiveSpacing.boundary_value n hn1 (by omega)
  have hB0 : 0 < value (UInt64.ofNat (n * 2 ^ 52)) := by rw [hB]; positivity
  rcases le_or_gt 0 y with hy0 | hy0
  · rw [abs_of_nonneg hy0] at hy
    exact within_one_of_error y c n hn E hcf hc hy hE (by linarith)
  · rw [abs_of_neg hy0] at hy
    have hnv := F64Magnitude.negate_value c hcf
    apply within_of_negate
    refine within_one_of_error (-y) _ n hn E hnv.1 ?_ hy hE (by linarith)
    rw [hnv.2, show -value c - -y = -(value c - y) by ring, abs_neg]
    exact hc

#print axioms rel_finish
#print axioms abs_finish

end LeanExe.ProofKit.F64WithinSelf
