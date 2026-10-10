import LeanExe.ProofKit.F64PositiveRounding
import LeanExe.ProofKit.F64PositiveOrder

/-!
The signed nearest-even reference and the count of representable steps between words.  Rounding
to nearest, ties to even, is symmetric, so the reference of a negative number is the negation of
the nonnegative reference of its magnitude.  `position` places every word on the ordered line of
binary64 values, with both zeros at 0 and the infinities next to the largest finite values, so
that `WithinSteps n y w` states that `w` is not a NaN and lies within `n` representable steps of
the reference of `y`.
-/

namespace LeanExe.ProofKit.F64SignedRounding
open CodeLib.IEEE64

/-- The nearest-even binary64 word of `y`, positive infinity from the overflow threshold on and
negative infinity from its negation down. -/
noncomputable def roundNearestEven (y : ℝ) : UInt64 :=
  if 0 ≤ y then F64PositiveRounding.roundNearestEven y
  else Wasm.IEEE64.negate (F64PositiveRounding.roundNearestEven (-y))

/-- The encoding of the magnitude of `w`, negated when the sign bit is set. -/
def position (w : UInt64) : Int :=
  if Wasm.IEEE64.sign w then -((w.toNat - 2 ^ 63 : Nat) : Int) else (w.toNat : Int)

/-- `w` is not a NaN and lies within `n` representable steps of the nearest-even reference of
`y`. -/
def WithinSteps (n : Nat) (y : ℝ) (w : UInt64) : Prop :=
  w.toNat % 2 ^ 63 ≤ 0x7FF0000000000000 ∧ |position w - position (roundNearestEven y)| ≤ n

theorem negate_toNat (w : UInt64) :
    (Wasm.IEEE64.negate w).toNat =
      if Wasm.IEEE64.sign w then w.toNat - 2 ^ 63 else w.toNat + 2 ^ 63 := by
  have hw := w.toNat_lt
  simp only [Wasm.IEEE64.negate, Wasm.IEEE64.encodeFinite, Wasm.IEEE64.sign,
    Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat']
  by_cases h : 2 ^ 63 ≤ w.toNat
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    omega
  · simp only [h, decide_false, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
    omega

theorem position_negate (w : UInt64) : position (Wasm.IEEE64.negate w) = -position w := by
  have hw := w.toNat_lt
  have hn := negate_toNat w
  unfold position Wasm.IEEE64.sign at *
  rw [hn]
  by_cases h : 2 ^ 63 ≤ w.toNat
  · simp only [h, decide_true, ite_true]
    have h' : ¬ 2 ^ 63 ≤ w.toNat - 2 ^ 63 := by omega
    simp only [h', decide_false, Bool.false_eq_true, ite_false]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    have h' : 2 ^ 63 ≤ w.toNat + 2 ^ 63 := by omega
    simp only [h', decide_true, ite_true]
    omega

theorem negate_magnitude (w : UInt64) :
    (Wasm.IEEE64.negate w).toNat % 2 ^ 63 = w.toNat % 2 ^ 63 := by
  have hw := w.toNat_lt
  rw [negate_toNat]
  unfold Wasm.IEEE64.sign
  by_cases h : 2 ^ 63 ≤ w.toNat
  · simp only [h, decide_true, ite_true]
    omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    omega

theorem positive_reference_le (y : ℝ) :
    (F64PositiveRounding.roundNearestEven y).toNat ≤ 0x7FF0000000000000 := by
  by_cases h : F64PositiveRounding.overflowThreshold ≤ y
  · rw [F64PositiveRounding.reference_overflow y h]
    decide
  · rw [F64PositiveRounding.reference_finite y (lt_of_not_ge h)]
    exact (F64NearestEven.roundNearestEven_spec y).1.1.le

theorem position_of_lt (w : UInt64) (hw : w.toNat < 2 ^ 63) : position w = w.toNat := by
  have h : ¬ 2 ^ 63 ≤ w.toNat := by omega
  simp only [position, Wasm.IEEE64.sign, h, decide_false, Bool.false_eq_true, ite_false]

/-- The reference of zero is positive zero. -/
theorem positive_reference_zero : F64PositiveRounding.roundNearestEven 0 = 0 := by
  rw [F64PositiveRounding.reference_finite 0 F64PositiveRounding.threshold_positive]
  have hs := F64NearestEven.roundNearestEven_spec 0
  by_contra hne
  have hpos : 0 < (F64NearestEven.roundNearestEven 0).toNat := by
    rcases Nat.eq_zero_or_pos (F64NearestEven.roundNearestEven 0).toNat with h | h
    · exact absurd (UInt64.toNat_inj.mp (h.trans (by decide))) hne
    · exact h
  have hlim : F64NearestNonnegative.limit < 2 ^ 63 := by decide
  have hlt := F64PositiveOrder.value_strict (hs.1.1.trans hlim)
    (show (0 : UInt64).toNat < (F64NearestEven.roundNearestEven 0).toNat by simpa using hpos)
  have hz : value (0 : UInt64) = 0 := by
    simp [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.sign,
      Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
  have hd := hs.1.2 0 (by decide)
  rw [hz, sub_zero, sub_zero, abs_zero] at hd
  rw [hz] at hlt
  have := abs_nonneg (value (F64NearestEven.roundNearestEven 0))
  rw [abs_of_pos hlt] at hd
  linarith

/-- Negating the number and the word preserves the count of steps. -/
theorem within_negate (n : Nat) (y : ℝ) (w : UInt64) :
    WithinSteps n (-y) (Wasm.IEEE64.negate w) ↔ WithinSteps n y w := by
  unfold WithinSteps
  rw [negate_magnitude, position_negate]
  have hr : position (roundNearestEven (-y)) = -position (roundNearestEven y) := by
    rcases lt_trichotomy y 0 with hy | hy | hy
    · have h1 : 0 ≤ -y := by linarith
      have h2 : ¬ 0 ≤ y := not_le.mpr hy
      simp only [roundNearestEven, h1, h2, ite_true, ite_false, position_negate, neg_neg]
    · subst hy
      have h0 : position (roundNearestEven 0) = 0 := by
        simp only [roundNearestEven, le_refl, ite_true, positive_reference_zero]
        rfl
      rw [neg_zero, h0, neg_zero]
    · have h1 : ¬ 0 ≤ -y := by linarith
      have h2 : 0 ≤ y := hy.le
      simp only [roundNearestEven, h1, h2, ite_true, ite_false, position_negate, neg_neg]
  rw [hr, show -position w - -position (roundNearestEven y) =
    -(position w - position (roundNearestEven y)) by ring, abs_neg]

/-- A nonnegative word within `n` steps of the nonnegative reference of a nonnegative number. -/
theorem within_of_nonneg (n : Nat) (y : ℝ) (hy : 0 ≤ y) (w : UInt64)
    (hw : w.toNat ≤ 0x7FF0000000000000)
    (h1 : w.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + n)
    (h2 : (F64PositiveRounding.roundNearestEven y).toNat ≤ w.toNat + n) :
    WithinSteps n y w := by
  have hr := positive_reference_le y
  have href : roundNearestEven y = F64PositiveRounding.roundNearestEven y := by
    simp only [roundNearestEven, hy, ite_true]
  refine ⟨by omega, ?_⟩
  rw [href, position_of_lt w (by omega), position_of_lt _ (by omega), abs_le]
  constructor <;> omega

/-- The negation of a nonnegative word within `n` steps of the reference of `-y`, for negative
`y`. -/
theorem within_of_neg (n : Nat) (y : ℝ) (hy : y < 0) (w : UInt64)
    (hw : w.toNat ≤ 0x7FF0000000000000)
    (h1 : w.toNat ≤ (F64PositiveRounding.roundNearestEven (-y)).toNat + n)
    (h2 : (F64PositiveRounding.roundNearestEven (-y)).toNat ≤ w.toNat + n) :
    WithinSteps n y (Wasm.IEEE64.negate w) := by
  have h := (within_negate n (-y) w).mpr (within_of_nonneg n (-y) (by linarith) w hw h1 h2)
  rwa [neg_neg] at h

#print axioms negate_toNat
#print axioms position_negate
#print axioms negate_magnitude
#print axioms positive_reference_le
#print axioms position_of_lt
#print axioms positive_reference_zero
#print axioms within_negate
#print axioms within_of_nonneg
#print axioms within_of_neg

end LeanExe.ProofKit.F64SignedRounding
