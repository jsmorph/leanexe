import LeanExe.ProofKit.F64PositiveRounding
import LeanExe.ProofKit.F64NearestBinade

/-!
A nonnegative word within one and a half spacings of a real number lies within one
representable step of the number's nearest-even reference, overflow included.  The words may
reach positive infinity, whose bits have the value `2 ^ 1024` under `value` and so continue the
spacing of the largest binade.
-/

namespace LeanExe.ProofKit.F64FullStep
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64NearestStep

set_option exponentiation.threshold 4096

/-- The spacing after word `n` is at least the spacing of binade `a` when `n` lies in or above
binade `a`.  Binade 0, the subnormals, has the spacing of binade 1. -/
theorem gap_lower (n a : Nat) (ha : a * 2 ^ 52 ≤ n) (hn : n + 1 < 2 ^ 63) :
    (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074 ≤
      value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n) := by
  have hw : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (lt_trans (Nat.lt_of_succ_lt hn) (by norm_num))
  have hg := F64Adjacent.positive_successor_gap (UInt64.ofNat n) (by rw [hw]; exact hn)
  have hi : UInt64.ofNat n + 1 = UInt64.ofNat (n + 1) := (UInt64.ofNat_add n 1).symm
  rw [hi, hw] at hg
  rw [hg]
  have hd : a ≤ n / 2 ^ 52 := (Nat.le_div_iff_mul_le (by positivity)).mpr ha
  gcongr
  all_goals norm_num

theorem below_largest_value :
    value (0x7FEFFFFFFFFFFFFE : UInt64) = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 972 := by
  have h : Wasm.IEEE64.scaledValue (0x7FEFFFFFFFFFFFFE : UInt64) =
      (2 : Int) ^ 2098 - (2 : Int) ^ 2046 := by decide +kernel
  rw [value, h]
  norm_num

/-- `F64NearestStep.one_step_of_spacing` with the range allowed to end at positive infinity. -/
theorem one_step_of_spacing_le (y d : ℝ) (c w : UInt64) (L U : Nat)
    (hd : 0 < d) (hU : U ≤ limit)
    (hc : L ≤ c.toNat ∧ c.toNat ≤ U)
    (hw : Nearest y w) (hwr : L ≤ w.toNat ∧ w.toNat ≤ U)
    (hspacing : ∀ n : Nat, L ≤ n → n < U →
      d ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n))
    (he : |value c - y| < 3 * d / 2) :
    c.toNat ≤ w.toNat + 1 ∧ w.toNat ≤ c.toNat + 1 := by
  have hlim : limit < 2 ^ 63 := by decide
  have hwl := hw.1
  have word_nat (n : Nat) (hn : n ≤ U) : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (lt_trans (lt_of_le_of_lt (hn.trans hU) hlim) (by norm_num))
  have hc63 : c.toNat < 2 ^ 63 := lt_of_le_of_lt (hc.2.trans hU) hlim
  constructor
  · by_contra h
    have hw1 : w.toNat + 1 ≤ U := by omega
    have hw2 : w.toNat + 2 ≤ U := by omega
    have hg1 := hspacing w.toNat hwr.1 (by omega)
    have hg2 := hspacing (w.toNat + 1) (by omega) (by omega)
    simp only [UInt64.ofNat_toNat] at hg1
    have hv : value w < value (UInt64.ofNat (w.toNat + 1)) := by linarith
    have hn : (UInt64.ofNat (w.toNat + 1)).toNat < limit := by
      rw [word_nat _ hw1]
      omega
    have hm := upper_midpoint _ _ y hv (hw.2 _ hn)
    have hc2 : value (UInt64.ofNat (w.toNat + 2)) ≤ value c := by
      apply (value_le_iff (by rw [word_nat _ hw2]; omega) hc63).mpr
      rw [word_nat _ hw2]
      omega
    have he' := (le_abs_self (value c - y)).trans_lt he
    norm_num only [Nat.add_assoc, Nat.reduceAdd] at hg2
    linarith
  · by_contra h
    have hmL : L ≤ w.toNat - 1 := by omega
    have hpL : L ≤ w.toNat - 2 := by omega
    have hmU : w.toNat - 1 ≤ U := by omega
    have hpU : w.toNat - 2 ≤ U := by omega
    have hg1 := hspacing (w.toNat - 1) hmL (by omega)
    have hg2 := hspacing (w.toNat - 2) hpL (by omega)
    have hmadd : w.toNat - 1 + 1 = w.toNat := by omega
    have hpadd : w.toNat - 2 + 1 = w.toNat - 1 := by omega
    rw [hmadd, UInt64.ofNat_toNat] at hg1
    rw [hpadd] at hg2
    have hv : value (UInt64.ofNat (w.toNat - 1)) < value w := by linarith
    have hn : (UInt64.ofNat (w.toNat - 1)).toNat < limit := by
      rw [word_nat _ hmU]
      omega
    have hm := lower_midpoint _ _ y hv (hw.2 _ hn)
    have hc2 : value c ≤ value (UInt64.ofNat (w.toNat - 2)) := by
      apply (value_le_iff hc63 (by rw [word_nat _ hpU]; omega)).mpr
      rw [word_nat _ hpU]
      omega
    have he' := (neg_le_abs (value c - y)).trans_lt he
    linarith

/-- A word `c` in the range `[L, U]`, where `U` may be positive infinity, with spacing at least
`d` and value within `3 d / 2` of `y`, lies within one step of the nearest-even reference of
`y`. -/
theorem one_step_full (y d : ℝ) (c : UInt64) (L U : Nat)
    (hd : 0 < d) (hdtop : d ≤ (2 : ℝ) ^ 971)
    (hL : L < limit) (hU : U ≤ limit)
    (hc : L ≤ c.toNat ∧ c.toNat ≤ U)
    (hyL : value (UInt64.ofNat L) ≤ y)
    (hyU : U < limit → y ≤ value (UInt64.ofNat U))
    (hspacing : ∀ n : Nat, L ≤ n → n < U →
      d ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n))
    (he : |value c - y| < 3 * d / 2) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + 1 := by
  have hlim : limit < 2 ^ 63 := by decide
  have hlim64 : limit < 2 ^ 64 := by decide
  by_cases ht : F64PositiveRounding.overflowThreshold ≤ y
  · rw [F64PositiveRounding.reference_overflow y ht]
    have hinf : F64PositiveRounding.positiveInfinity.toNat = limit := by decide
    rw [hinf]
    refine ⟨by omega, ?_⟩
    by_contra hn
    have hcl : c.toNat ≤ (0x7FEFFFFFFFFFFFFE : UInt64).toNat := by
      have hl : limit = 0x7FF0000000000000 := rfl
      change c.toNat ≤ 0x7FEFFFFFFFFFFFFE
      omega
    have hv := (value_le_iff (lt_of_le_of_lt (hc.2.trans hU) hlim)
      (by decide : (0x7FEFFFFFFFFFFFFE : UInt64).toNat < 2 ^ 63)).mpr hcl
    rw [below_largest_value] at hv
    have hth : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 := rfl
    rw [hth] at ht
    have he' := (neg_le_abs (value c - y)).trans_lt he
    have h972 : (2 : ℝ) ^ 972 = 4 * (2 : ℝ) ^ 970 := by norm_num
    have h971 : (2 : ℝ) ^ 971 = 2 * (2 : ℝ) ^ 970 := by norm_num
    linarith
  · have hyt : y < F64PositiveRounding.overflowThreshold := lt_of_not_ge ht
    rw [F64PositiveRounding.reference_finite y hyt]
    have hw : Nearest y (F64NearestEven.roundNearestEven y) :=
      (F64NearestEven.roundNearestEven_spec y).1
    have hLw : (UInt64.ofNat L).toNat = L :=
      UInt64.toNat_ofNat_of_lt' (hL.trans hlim64)
    have hwL : L ≤ (F64NearestEven.roundNearestEven y).toNat := by
      by_contra hn
      have hlt := value_strict (by rw [hLw]; exact hL.trans hlim)
        (show (F64NearestEven.roundNearestEven y).toNat < (UInt64.ofNat L).toNat by
          rw [hLw]; omega)
      have hd' := hw.2 (UInt64.ofNat L) (by rw [hLw]; exact hL)
      rw [abs_of_nonpos (by linarith : value (F64NearestEven.roundNearestEven y) - y ≤ 0),
        abs_of_nonpos (by linarith : value (UInt64.ofNat L) - y ≤ 0)] at hd'
      linarith
    have hwU : (F64NearestEven.roundNearestEven y).toNat ≤ U := by
      rcases Nat.lt_or_ge U limit with hUl | hUl
      · have hUw : (UInt64.ofNat U).toNat = U :=
          UInt64.toNat_ofNat_of_lt' (hUl.trans hlim64)
        have hi := nearest_interval y _ (UInt64.ofNat L) (UInt64.ofNat U) hw
          (by rw [hLw]; exact hL) (by rw [hUw]; exact hUl) hyL (hyU hUl)
        rw [hUw] at hi
        exact hi.2
      · exact le_trans (Nat.le_of_lt hw.1) hUl
    exact one_step_of_spacing_le y d c _ L U hd hU hc hw ⟨hwL, hwU⟩ hspacing he

theorem infinity_value : value (0x7FF0000000000000 : UInt64) = (2 : ℝ) ^ 1024 := by
  have h : Wasm.IEEE64.scaledValue (0x7FF0000000000000 : UInt64) = (2 : Int) ^ 2098 := by
    decide +kernel
  rw [value, h]
  norm_num

/-- `one_step_full` for a word and a number between the boundaries of binades `a` and `b`, where
binade 2047 starts at positive infinity, with an error below one and a half spacings of binade
`a`. -/
theorem one_step_binades (y : ℝ) (c : UInt64) (a b : Nat) (hab : a < b) (hb : b ≤ 2047)
    (hya : value (UInt64.ofNat (a * 2 ^ 52)) ≤ y)
    (hyb : b < 2047 → y ≤ value (UInt64.ofNat (b * 2 ^ 52)))
    (hc63 : c.toNat < 2 ^ 63)
    (hca : value (UInt64.ofNat (a * 2 ^ 52)) ≤ value c)
    (hcb : value c ≤ value (UInt64.ofNat (b * 2 ^ 52)))
    (he : |value c - y| < 3 * ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074) / 2) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + 1 := by
  have hlim : limit < 2 ^ 63 := by decide
  have hl : limit = 2047 * 2 ^ 52 := rfl
  have hbn : b * 2 ^ 52 ≤ limit := by rw [hl]; omega
  have han : a * 2 ^ 52 < limit := by rw [hl]; omega
  have word (n : Nat) (hn : n ≤ limit) : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (lt_trans (lt_of_le_of_lt hn hlim) (by norm_num))
  have hcL : a * 2 ^ 52 ≤ c.toNat := by
    have h := (value_le_iff (by rw [word _ han.le]; exact han.trans hlim) hc63).mp hca
    rwa [word _ han.le] at h
  have hcU : c.toNat ≤ b * 2 ^ 52 := by
    have h := (value_le_iff hc63 (by rw [word _ hbn]; exact lt_of_le_of_lt hbn hlim)).mp hcb
    rwa [word _ hbn] at h
  refine one_step_full y ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074) c (a * 2 ^ 52) (b * 2 ^ 52)
    (by positivity) ?_ han hbn ⟨hcL, hcU⟩ hya ?_ ?_ he
  · calc
      (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074 ≤ (2 : ℝ) ^ 2045 / (2 : ℝ) ^ 1074 := by
        gcongr
        all_goals first | omega | norm_num
      _ = (2 : ℝ) ^ 971 := by norm_num
  · intro hbl
    apply hyb
    rw [hl] at hbl
    omega
  · intro n hn1 hn2
    exact gap_lower n a hn1 (by rw [hl] at hbn; omega)

#print axioms gap_lower
#print axioms below_largest_value
#print axioms one_step_of_spacing_le
#print axioms one_step_full
#print axioms infinity_value
#print axioms one_step_binades

end LeanExe.ProofKit.F64FullStep
