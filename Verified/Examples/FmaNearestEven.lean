import Verified.Examples.FmaGrid

/-!
The nearest-even rounding of a nonnegative number given in units of `2 ^ -2400`, in the form that
`Fma.roundPack` computes it.  When `RoundsTo Y E Q` holds (`FmaGrid`), `positive_reference` proves
that the nearest-even reference of `Y · 2 ^ -2400` is the word `(E - 1) · 2 ^ 52 + Q`, or positive
infinity when that word or `E` reaches the exponent field 2047 (`FmaGrid.packWord`).  Every double
at or above the start of the binade is a multiple of the spacing, so none is closer than `Q`
spacings, and every double below the start is farther than the start.  Away from a tie, every
other double is farther than `Q` spacings, which gives the even choice.  `signed_reference` adds the
sign.
-/

namespace Verified.Examples.FmaNearestEven
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative FmaGrid

set_option exponentiation.threshold 4096

/-- The nearest-even word of `Y · 2 ^ -2400` below the overflow threshold. -/
theorem nearest_even (Y E Q : ℕ) (h : RoundsTo Y E Q)
    (hW : (E - 1) * 2 ^ 52 + Q < 0x7FF0000000000000) :
    NearestEven ((Y : ℝ) / 2 ^ 2400) (UInt64.ofNat ((E - 1) * 2 ^ 52 + Q)) := by
  obtain ⟨hQ, hQ52⟩ := significand_bounds Y E Q h
  obtain ⟨hE, hY53, hY52, hr1, hr2, htie⟩ := h
  obtain ⟨hWn, hWs, hWv⟩ := word_value E Q hE hQ hQ52 hW
  generalize UInt64.ofNat ((E - 1) * 2 ^ 52 + Q) = w at hWn hWs hWv ⊢
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = ((spacing E : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hsdef] at hWv
  have hs : 0 < s := by rw [hsdef]; exact_mod_cast spacing_pos E
  have hu : (0 : ℝ) < 2 ^ 2400 := by positivity
  have hwl : w.toNat < limit := by rw [hWn]; exact hW
  have r1 : 2 * (Y : ℝ) ≤ (2 * Q + 1) * s := by rw [hsdef]; exact_mod_cast hr1
  have r2 : 2 * (Q : ℝ) * s ≤ 2 * Y + s := by rw [hsdef]; exact_mod_cast hr2
  have hwv : value w = (Q : ℝ) * s / 2 ^ 2400 := hWv
  -- every nonnegative word is at least as far as `w`, and farther unless it is `w`
  have key : ∀ v : UInt64, v.toNat < limit →
      |(Q : ℝ) * s - Y| ≤ |((Wasm.IEEE64.scaledMagnitude v * 2 ^ 1326 : ℕ) : ℝ) - Y| ∧
      (Q % 2 = 1 → |((Wasm.IEEE64.scaledMagnitude v * 2 ^ 1326 : ℕ) : ℝ) - Y| ≤
        |(Q : ℝ) * s - Y| → v = w) := by
    intro v hv
    rcases grid_or_below v E hE with ⟨j, hj⟩ | ⟨hE2, hb⟩
    · rw [hj, Nat.cast_mul, ← hsdef]
      refine ⟨grid_near Y s Q j hs r1 r2, fun hodd hle => ?_⟩
      have n1 : 2 * Y < (2 * Q + 1) * spacing E := by
        rcases lt_or_eq_of_le hr1 with h' | h'
        · exact h'
        · have := htie (Or.inl h'); omega
      have n2 : 2 * Q * spacing E < 2 * Y + spacing E := by
        rcases lt_or_eq_of_le hr2 with h' | h'
        · exact h'
        · have := htie (Or.inr h'.symm); omega
      have m1 : 2 * (Y : ℝ) < (2 * Q + 1) * s := by rw [hsdef]; exact_mod_cast n1
      have m2 : 2 * (Q : ℝ) * s < 2 * Y + s := by rw [hsdef]; exact_mod_cast n2
      have hjQ := grid_unique Y s Q j hs m1 m2 hle
      rw [hjQ] at hj
      have hval : value v = value w := by
        rw [nonneg_value v hv, hj, hwv, Nat.cast_mul, ← hsdef]
      have hlim : limit < 2 ^ 63 := by decide
      apply UInt64.toNat_inj.mp
      rcases lt_trichotomy v.toNat w.toNat with h' | h' | h'
      · exact absurd hval (ne_of_lt (F64PositiveOrder.value_strict (hwl.trans hlim) h'))
      · exact h'
      · exact absurd hval (ne_of_gt (F64PositiveOrder.value_strict (hv.trans hlim) h'))
    · have hY52' : 2 ^ 52 * spacing E ≤ Y := by
        rcases hY52 with h' | h'
        · omega
        · exact h'
      have hQ52' : 2 ^ 52 ≤ Q := by
        rcases hQ52 with h' | h'
        · omega
        · exact h'
      have b1 : 2 * ((Wasm.IEEE64.scaledMagnitude v * 2 ^ 1326 : ℕ) : ℝ) + s ≤
          2 * ((2 : ℝ) ^ 52 * s) := by
        rw [hsdef]
        have : (2 * (Wasm.IEEE64.scaledMagnitude v * 2 ^ 1326) + spacing E : ℕ) ≤
            2 * (2 ^ 52 * spacing E) := by
          rw [show 2 * (2 ^ 52 * spacing E) = 2 ^ 53 * spacing E by ring]
          exact hb
        exact_mod_cast this
      have b2 : (2 : ℝ) ^ 52 * s ≤ Y := by rw [hsdef]; exact_mod_cast hY52'
      have b3 : (2 : ℝ) ^ 52 * s ≤ Q * s := by
        apply mul_le_mul_of_nonneg_right _ hs.le
        exact_mod_cast hQ52'
      have r2' : 2 * ((Q : ℝ) * s) ≤ 2 * Y + s := by rw [← mul_assoc]; exact r2
      obtain ⟨f1, f2⟩ := below_far Y s _ _ _ hs b1 b2 b3 r2'
      refine ⟨f1, fun hodd hle => ?_⟩
      exfalso
      have n1 : 2 * Y < (2 * Q + 1) * spacing E := by
        rcases lt_or_eq_of_le hr1 with h' | h'
        · exact h'
        · have := htie (Or.inl h'); omega
      have n2 : 2 * Q * spacing E < 2 * Y + spacing E := by
        rcases lt_or_eq_of_le hr2 with h' | h'
        · exact h'
        · have := htie (Or.inr h'.symm); omega
      have m1 : 2 * (Y : ℝ) < (2 * Q + 1) * s := by rw [hsdef]; exact_mod_cast n1
      have m2 : 2 * (Q : ℝ) * s < 2 * Y + s := by rw [hsdef]; exact_mod_cast n2
      have e1 : (2 * (Q : ℝ) + 1) * s = 2 * (Q * s) + s := by ring
      have e2 : 2 * (Q : ℝ) * s = 2 * (Q * s) := by ring
      rw [e1] at m1
      rw [e2] at m2
      have hq : |(Q : ℝ) * s - Y| < s / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
      exact lt_irrefl _ (lt_of_le_of_lt (f2.trans hle) hq)
  have hnear : Nearest ((Y : ℝ) / 2 ^ 2400) w := by
    refine ⟨hwl, fun v hv => ?_⟩
    rw [hwv, nonneg_value v hv, dist_div _ _ _ hu, dist_div _ _ _ hu]
    exact div_le_div_of_nonneg_right (key v hv).1 hu.le
  refine ⟨hnear, fun v hv => ?_⟩
  have hW2 : w.toNat % 2 = Q % 2 := by
    rw [hWn]; simp only [Nat.reducePow]; omega
  rcases Nat.mod_two_eq_zero_or_one Q with hq | hq
  · rw [hW2, hq]; exact Nat.zero_le _
  · have hle := hv.2 w hwl
    rw [hwv, nonneg_value v hv.1, dist_div _ _ _ hu, dist_div _ _ _ hu] at hle
    have hle' := (div_le_div_iff_of_pos_right hu).mp hle
    have hvw := (key v hv.1).2 hq hle'
    rw [hvw]

theorem threshold_eq : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - 2 ^ 970 := rfl

/-- At or above the start of binade 2047 a number is beyond the overflow threshold. -/
theorem overflow_large (Y E : ℕ) (hE : 2047 ≤ E) (hY : 2 ^ 52 * spacing E ≤ Y) :
    F64PositiveRounding.overflowThreshold ≤ (Y : ℝ) / 2 ^ 2400 := by
  have hu : (0 : ℝ) < 2 ^ 2400 := by positivity
  have hYr : (2 : ℝ) ^ 52 * ((spacing E : ℕ) : ℝ) ≤ Y := by exact_mod_cast hY
  rw [spacing_real] at hYr
  have hS : (2 : ℝ) ^ 3372 ≤ 2 ^ (E + 1325) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [threshold_eq, le_div_iff₀ hu]
  have : ((2 : ℝ) ^ 1024 - 2 ^ 970) * 2 ^ 2400 ≤ 2 ^ 52 * 2 ^ 3372 := by norm_num
  linarith

/-- The rounding up to `2 ^ 53` spacings of binade 2046 reaches the overflow threshold. -/
theorem overflow_top (Y : ℕ)
    (hr2 : 2 * 9007199254740992 * spacing 2046 ≤ 2 * Y + spacing 2046) :
    F64PositiveRounding.overflowThreshold ≤ (Y : ℝ) / 2 ^ 2400 := by
  have hu : (0 : ℝ) < 2 ^ 2400 := by positivity
  have hr : (2 : ℝ) * 9007199254740992 * ((spacing 2046 : ℕ) : ℝ) ≤
      2 * Y + ((spacing 2046 : ℕ) : ℝ) := by exact_mod_cast hr2
  rw [spacing_real] at hr
  rw [threshold_eq, le_div_iff₀ hu]
  have : ((2 : ℝ) ^ 1024 - 2 ^ 970) * 2 ^ 2400 =
      (2 * 9007199254740992 - 1) / 2 * 2 ^ (2046 + 1325) := by norm_num
  rw [this]
  generalize (2 : ℝ) ^ (2046 + 1325) = t at hr ⊢
  linarith

/-- Below binade 2046 a number is below the overflow threshold. -/
theorem below_low (Y E : ℕ) (hE : E ≤ 2045) (hY53 : Y < 2 ^ 53 * spacing E) :
    (Y : ℝ) / 2 ^ 2400 < F64PositiveRounding.overflowThreshold := by
  have hu : (0 : ℝ) < 2 ^ 2400 := by positivity
  rw [threshold_eq, div_lt_iff₀ hu]
  have hYr : (Y : ℝ) < 2 ^ 53 * ((spacing E : ℕ) : ℝ) := by exact_mod_cast hY53
  rw [spacing_real] at hYr
  have hS : (2 : ℝ) ^ (E + 1325) ≤ 2 ^ 3370 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have : (2 : ℝ) ^ 53 * 2 ^ 3370 ≤ (2 ^ 1024 - 2 ^ 970) * 2 ^ 2400 := by norm_num
  linarith

theorem below_top (Y : ℕ)
    (hstrict : 2 * Y < (2 * 9007199254740991 + 1) * spacing 2046) :
    (Y : ℝ) / 2 ^ 2400 < F64PositiveRounding.overflowThreshold := by
  have hu : (0 : ℝ) < 2 ^ 2400 := by positivity
  rw [threshold_eq, div_lt_iff₀ hu]
  have hYr : (2 : ℝ) * Y < (2 * 9007199254740991 + 1) * ((spacing 2046 : ℕ) : ℝ) := by
    exact_mod_cast hstrict
  rw [spacing_real] at hYr
  have : ((2 : ℝ) ^ 1024 - 2 ^ 970) * 2 ^ 2400 =
      (2 * 9007199254740991 + 1) / 2 * 2 ^ (2046 + 1325) := by norm_num
  rw [this]
  generalize (2 : ℝ) ^ (2046 + 1325) = t at hYr ⊢
  linarith

theorem strict_top (Y Q S : ℕ) (hQ : Q ≤ 9007199254740991) (hS : 0 < S)
    (hr1 : 2 * Y ≤ (2 * Q + 1) * S)
    (htie : 2 * Y = (2 * Q + 1) * S ∨ 2 * Y + S = 2 * Q * S → Q % 2 = 0) :
    2 * Y < (2 * 9007199254740991 + 1) * S := by
  rcases lt_or_ge Q 9007199254740991 with hq | hq
  · have : (2 * Q + 1) * S < (2 * 9007199254740991 + 1) * S :=
      Nat.mul_lt_mul_of_pos_right (by omega) hS
    omega
  · have hq' : Q = 9007199254740991 := by omega
    rcases lt_or_eq_of_le hr1 with h1 | h1
    · rw [hq'] at h1; exact h1
    · have := htie (Or.inl h1)
      omega

/-- The nearest-even reference of a nonnegative `Y · 2 ^ -2400` is the packed word. -/
theorem positive_reference (Y E Q : ℕ) (h : RoundsTo Y E Q) :
    F64PositiveRounding.roundNearestEven ((Y : ℝ) / 2 ^ 2400) = packWord 0 E Q := by
  obtain ⟨hQ, hQ52⟩ := significand_bounds Y E Q h
  have h' := h
  obtain ⟨hE, hY53, hY52, hr1, hr2, htie⟩ := h'
  have hinf : ((0 : UInt64) <<< 63) ||| 0x7FF0000000000000 =
      F64PositiveRounding.positiveInfinity := by decide +kernel
  unfold packWord
  by_cases hE2047 : 2047 ≤ E
  · rw [ite_eq_left hE2047, hinf]
    apply F64PositiveRounding.reference_overflow
    apply overflow_large Y E hE2047
    rcases hY52 with h1 | h1
    · omega
    · exact h1
  rw [ite_eq_right hE2047]
  by_cases hW : 0x7FF0000000000000 ≤ (E - 1) * 2 ^ 52 + Q
  · rw [ite_eq_left hW, hinf]
    apply F64PositiveRounding.reference_overflow
    simp only [Nat.reducePow] at hQ hW
    have hE' : E = 2046 := by omega
    have hQ' : Q = 9007199254740992 := by omega
    rw [hE', hQ'] at hr2
    exact overflow_top Y hr2
  rw [ite_eq_right hW]
  have hzero : ∀ w : UInt64, ((0 : UInt64) <<< 63) ||| w = w := by
    intro w; simp
  rw [hzero]
  have hy : (Y : ℝ) / 2 ^ 2400 < F64PositiveRounding.overflowThreshold := by
    by_cases hE2046 : E ≤ 2045
    · exact below_low Y E hE2046 hY53
    · have hE' : E = 2046 := by omega
      rw [hE'] at hr1 htie hW
      simp only [Nat.reducePow] at hQ hW
      exact below_top Y (strict_top Y Q (spacing 2046) (by omega) (spacing_pos _) hr1 htie)
  rw [F64PositiveRounding.reference_finite _ hy]
  exact F64NearestEven.roundNearestEven_eq _ _ (nearest_even Y E Q h (by omega))

/-- The packed word of sign 1 is the negation of the packed word of sign 0. -/
theorem pack_negative (E Q : ℕ) :
    packWord 1 E Q = Wasm.IEEE64.negate (packWord 0 E Q) := by
  have hneg : ∀ w : UInt64, w.toNat < 2 ^ 63 →
      ((1 : UInt64) <<< 63) ||| w = Wasm.IEEE64.negate (((0 : UInt64) <<< 63) ||| w) := by
    intro w hw
    have hz : ((0 : UInt64) <<< 63) ||| w = w := by simp
    rw [hz]
    apply UInt64.toNat_inj.mp
    rw [or_sign w hw, F64SignedRounding.negate_toNat]
    have : Wasm.IEEE64.sign w = false := by
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]; exact hw
    rw [this]
    simp only [Bool.false_eq_true, ite_false]
    omega
  unfold packWord
  split_ifs with h1 h2
  · exact hneg _ (by decide +kernel)
  · exact hneg _ (by decide +kernel)
  · apply hneg
    have h2' : (E - 1) * 2 ^ 52 + Q < 0x7FF0000000000000 := by omega
    rw [UInt64.toNat_ofNat_of_lt' (lt_trans h2' (by decide))]
    exact lt_trans h2' (by decide)

/-- The signed nearest-even reference of `±Y · 2 ^ -2400`, `Y > 0`, is the packed word. -/
theorem signed_reference (Y E Q : ℕ) (s : UInt64) (hs : s = 0 ∨ s = 1) (hY : 0 < Y)
    (h : RoundsTo Y E Q) :
    F64SignedRounding.roundNearestEven ((if s = 1 then -(Y : ℝ) else Y) / 2 ^ 2400) =
      packWord s E Q := by
  have hYr : (0 : ℝ) < Y / 2 ^ 2400 := by
    have : (0 : ℝ) < Y := by exact_mod_cast hY
    positivity
  rcases hs with rfl | rfl
  · rw [ite_eq_right (by decide), F64SignedRounding.roundNearestEven, ite_eq_left hYr.le]
    exact positive_reference Y E Q h
  · rw [ite_eq_left rfl, F64SignedRounding.roundNearestEven,
      ite_eq_right (not_le.mpr (by rw [neg_div]; linarith)), neg_div, neg_neg,
      positive_reference Y E Q h, pack_negative]

#print axioms nearest_even
#print axioms overflow_top
#print axioms below_top
#print axioms positive_reference
#print axioms pack_negative
#print axioms signed_reference

end Verified.Examples.FmaNearestEven
