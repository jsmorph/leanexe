import LeanExe.ProofKit.F64RelativeStep

/-!
`m` representable steps from relative and absolute errors.  A word whose value lies within
`(2 m + 1)/2` spacings of `y`, in a range of words whose spacing is at least `d`, lies within `m`
steps of the nearest word to `y`: the `m + 1` gaps above the nearest word reach past the midpoint
above it by `m` spacings.  `within_steps_relative` turns a relative error of at most `(m + 3/8)`
units of roundoff into `F64SignedRounding.WithinSteps m`, as `F64RelativeStep.within_one_relative`
does for one step, for `|y|` at least `17/16 · 2^-1022`.  `within_steps_low` does the same for a
nonnegative `y` and a nonnegative word from an absolute error below `(2 m + 1)/2 · 2^-1074`, the
least spacing of binary64 values.
-/

namespace LeanExe.ProofKit.F64RelativeSteps
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64NearestStep F64Magnitude

set_option exponentiation.threshold 4096

/-- `k` consecutive gaps of at least `d` add up to at least `k d`. -/
theorem gap_sum (L U : Nat) (d : ℝ) (hU : U ≤ limit)
    (hspacing : ∀ n : Nat, L ≤ n → n < U →
      d ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n)) :
    ∀ k n : Nat, L ≤ n → n + k ≤ U →
      (k : ℝ) * d ≤ value (UInt64.ofNat (n + k)) - value (UInt64.ofNat n) := by
  intro k
  induction k with
  | zero => intro n _ _; simp
  | succ k ih =>
    intro n hn hk
    have h1 := ih n hn (by omega)
    have h2 := hspacing (n + k) (by omega) (by omega)
    rw [show n + (k + 1) = n + k + 1 by ring]
    push_cast
    linarith

/-- `F64FullStep.one_step_of_spacing_le` for `m ≥ 1` steps. -/
theorem steps_of_spacing_le (m : Nat) (hm : 1 ≤ m) (y d : ℝ) (c w : UInt64) (L U : Nat)
    (hd : 0 < d) (hU : U ≤ limit)
    (hc : L ≤ c.toNat ∧ c.toNat ≤ U)
    (hw : Nearest y w) (hwr : L ≤ w.toNat ∧ w.toNat ≤ U)
    (hspacing : ∀ n : Nat, L ≤ n → n < U →
      d ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n))
    (he : |value c - y| < (2 * m + 1) * d / 2) :
    c.toNat ≤ w.toNat + m ∧ w.toNat ≤ c.toNat + m := by
  have hlim : limit < 2 ^ 63 := by decide
  have word_nat (n : Nat) (hn : n ≤ U) : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (lt_trans (lt_of_le_of_lt (hn.trans hU) hlim) (by norm_num))
  have hc63 : c.toNat < 2 ^ 63 := lt_of_le_of_lt (hc.2.trans hU) hlim
  have hgs := gap_sum L U d hU hspacing
  constructor
  · by_contra h
    have hw1 : w.toNat + 1 ≤ U := by omega
    have hwm : w.toNat + 1 + m ≤ U := by omega
    have hg1 := hspacing w.toNat hwr.1 (by omega)
    simp only [UInt64.ofNat_toNat] at hg1
    have hgm := hgs m (w.toNat + 1) (by omega) hwm
    have hv : value w < value (UInt64.ofNat (w.toNat + 1)) := by linarith
    have hn : (UInt64.ofNat (w.toNat + 1)).toNat < limit := by
      rw [word_nat _ hw1]
      omega
    have hmid := upper_midpoint _ _ y hv (hw.2 _ hn)
    have hcm : value (UInt64.ofNat (w.toNat + 1 + m)) ≤ value c := by
      apply (value_le_iff (by rw [word_nat _ hwm]; omega) hc63).mpr
      rw [word_nat _ hwm]
      omega
    have he' := (le_abs_self (value c - y)).trans_lt he
    have hmd : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  · by_contra h
    have hwL : L + 1 + m ≤ w.toNat := by omega
    have hgm := hgs m (w.toNat - 1 - m) (by omega) (by omega)
    have hg1 := hspacing (w.toNat - 1) (by omega) (by omega)
    have hpadd : w.toNat - 1 - m + m = w.toNat - 1 := by omega
    have hmadd : w.toNat - 1 + 1 = w.toNat := by omega
    rw [hpadd] at hgm
    rw [hmadd, UInt64.ofNat_toNat] at hg1
    have hv : value (UInt64.ofNat (w.toNat - 1)) < value w := by linarith
    have hn : (UInt64.ofNat (w.toNat - 1)).toNat < limit := by
      rw [word_nat _ (by omega)]
      omega
    have hmid := lower_midpoint _ _ y hv (hw.2 _ hn)
    have hcm : value c ≤ value (UInt64.ofNat (w.toNat - 1 - m)) := by
      apply (value_le_iff hc63 (by rw [word_nat _ (by omega)]; omega)).mpr
      rw [word_nat _ (by omega)]
      omega
    have he' := (neg_le_abs (value c - y)).trans_lt he
    have hmd : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith

/-- The value of the word `m + 1` below positive infinity. -/
theorem below_infinity_value (m : Nat) (hm : m + 1 ≤ 2 ^ 52) :
    value (UInt64.ofNat (limit - (m + 1))) = (2 : ℝ) ^ 1024 - (m + 1) * (2 : ℝ) ^ 971 := by
  have hl : limit = 2047 * 2 ^ 52 := rfl
  have hsz : UInt64.size = 18446744073709551616 := rfl
  have hw : (UInt64.ofNat (limit - (m + 1))).toNat = 2046 * 2 ^ 52 + (2 ^ 52 - (m + 1)) := by
    rw [UInt64.toNat_ofNat_of_lt' (by rw [hl]; omega), hl]
    omega
  have hs : Wasm.IEEE64.sign (UInt64.ofNat (limit - (m + 1))) = false := by
    simp only [Wasm.IEEE64.sign, hw, decide_eq_false_iff_not, not_le]
    omega
  have he : Wasm.IEEE64.exponent (UInt64.ofNat (limit - (m + 1))) = 2046 := by
    simp only [Wasm.IEEE64.exponent, hw]
    omega
  have hf : Wasm.IEEE64.fraction (UInt64.ofNat (limit - (m + 1))) = 2 ^ 52 - (m + 1) := by
    simp only [Wasm.IEEE64.fraction, hw]
    omega
  rw [normal_value _ hs (by rw [he]; norm_num), he, hf]
  have hc : ((2 ^ 52 - (m + 1) : Nat) : ℝ) = 2 ^ 52 - (m + 1) := by
    rw [Nat.cast_sub hm]
    push_cast
    ring
  rw [hc]
  norm_num
  ring

/-- `F64FullStep.one_step_full` for `m ≥ 1` steps. -/
theorem steps_full (m : Nat) (hm : 1 ≤ m) (hm52 : m + 1 ≤ 2 ^ 52) (y d : ℝ) (c : UInt64)
    (L U : Nat) (hd : 0 < d) (hdtop : d ≤ (2 : ℝ) ^ 971)
    (hL : L < limit) (hU : U ≤ limit)
    (hc : L ≤ c.toNat ∧ c.toNat ≤ U)
    (hyL : value (UInt64.ofNat L) ≤ y)
    (hyU : U < limit → y ≤ value (UInt64.ofNat U))
    (hspacing : ∀ n : Nat, L ≤ n → n < U →
      d ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n))
    (he : |value c - y| < (2 * m + 1) * d / 2) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + m ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + m := by
  have hlim : limit < 2 ^ 63 := by decide
  have hlim64 : limit < 2 ^ 64 := by decide
  by_cases ht : F64PositiveRounding.overflowThreshold ≤ y
  · rw [F64PositiveRounding.reference_overflow y ht]
    have hinf : F64PositiveRounding.positiveInfinity.toNat = limit := by decide
    have hsz : UInt64.size = 18446744073709551616 := rfl
    have hl : limit = 9218868437227405312 := rfl
    rw [hinf]
    refine ⟨by omega, ?_⟩
    by_contra hn
    have hcl : c.toNat ≤ (UInt64.ofNat (limit - (m + 1))).toNat := by
      rw [UInt64.toNat_ofNat_of_lt' (by omega)]
      omega
    have hv := (value_le_iff (lt_of_le_of_lt (hc.2.trans hU) hlim)
      (by rw [UInt64.toNat_ofNat_of_lt' (by omega)]; omega)).mpr hcl
    rw [below_infinity_value m hm52] at hv
    have hth : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 := rfl
    rw [hth] at ht
    have he' := (neg_le_abs (value c - y)).trans_lt he
    have h971 : (2 : ℝ) ^ 971 = 2 * (2 : ℝ) ^ 970 := by norm_num
    have hmd : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
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
    exact steps_of_spacing_le m hm y d c _ L U hd hU hc hw ⟨hwL, hwU⟩ hspacing he

/-- `F64FullStep.one_step_binades` for `m ≥ 1` steps. -/
theorem steps_binades (m : Nat) (hm : 1 ≤ m) (hm52 : m + 1 ≤ 2 ^ 52) (y : ℝ) (c : UInt64)
    (a b : Nat) (hab : a < b) (hb : b ≤ 2047)
    (hya : value (UInt64.ofNat (a * 2 ^ 52)) ≤ y)
    (hyb : b < 2047 → y ≤ value (UInt64.ofNat (b * 2 ^ 52)))
    (hc63 : c.toNat < 2 ^ 63)
    (hca : value (UInt64.ofNat (a * 2 ^ 52)) ≤ value c)
    (hcb : value c ≤ value (UInt64.ofNat (b * 2 ^ 52)))
    (he : |value c - y| < (2 * m + 1) * ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074) / 2) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + m ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + m := by
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
  refine steps_full m hm hm52 y ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074) c (a * 2 ^ 52) (b * 2 ^ 52)
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
    exact F64FullStep.gap_lower n a hn1 (by rw [hl] at hbn; omega)

/-- The power of two at the start of binade `e`. -/
private theorem zpow_eq (e : Nat) (he : 1 ≤ e) :
    (2 : ℝ) ^ ((e : Int) - 1023) = (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 := by
  rw [eq_div_iff (by positivity), ← zpow_natCast (2 : ℝ) (e - 1), ← zpow_natCast (2 : ℝ) 1022,
    ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

private theorem boundary_pow (e : Nat) (he1 : 1 ≤ e) (he2 : e < 2048) :
    value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1022 := by
  rw [← zpow_eq e he1]
  exact F64NearestBinade.boundary_power e ((e : Int) - 1023) he1 he2 (by ring)

/-- A finite word within `m + 3/8` units of roundoff of a positive `y`, relative to `y`, lies within
`m` steps of the nonnegative nearest-even reference of `y`, for `1 ≤ m ≤ 64`. -/
theorem steps_relative (m : Nat) (hm : 1 ≤ m) (hm64 : m ≤ 64) (y : ℝ) (c : UInt64)
    (hcf : Finite c) (hy : (17 / 16) / (2 : ℝ) ^ 1022 ≤ y)
    (hc : |value c - y| ≤ (m + 3 / 8) * unitRoundoff64 * y) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + m ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + m := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmr64 : (m : ℝ) ≤ 64 := by exact_mod_cast hm64
  set k : ℝ := (m + 3 / 8) * unitRoundoff64 with hk
  have hk0 : 0 < k := by rw [hk, hu]; positivity
  have hk1 : (m + 1 / 2 : ℝ) * k ≤ 1 / 8 := by
    rw [hk, hu]
    have : (m + 1 / 2 : ℝ) * ((m + 3 / 8) * (1 / 2 ^ 53)) ≤ 65 * (65 * (1 / 2 ^ 53)) := by
      gcongr <;> linarith
    linarith [show (65 : ℝ) * (65 * (1 / 2 ^ 53)) ≤ 1 / 8 by norm_num]
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hy
  have hky : k * y ≤ y / 8 := by
    have h1 : k ≤ 1 / 8 := by nlinarith
    nlinarith
  have hcl := (abs_le.mp hc).1
  have hcu := (abs_le.mp hc).2
  have hcy : y / 2 ≤ value c := by linarith
  have hk65 : k ≤ 65 / 2 ^ 53 := by
    rw [hk, hu]
    have : (m + 3 / 8 : ℝ) ≤ 65 := by linarith
    calc (m + 3 / 8 : ℝ) * (1 / 2 ^ 53) ≤ 65 * (1 / 2 ^ 53) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 65 / 2 ^ 53 := by ring
  have hcn : 1 / (2 : ℝ) ^ 1022 < value c := by
    have h1 : k * y ≤ 65 / 2 ^ 53 * y := mul_le_mul_of_nonneg_right hk65 hy0.le
    have h2 : (17 / 16) / (2 : ℝ) ^ 1022 * (1 - 65 / 2 ^ 53) ≤ y * (1 - 65 / 2 ^ 53) :=
      mul_le_mul_of_nonneg_right hy (by norm_num)
    have h3 : 1 / (2 : ℝ) ^ 1022 < (17 / 16) / (2 : ℝ) ^ 1022 * (1 - 65 / 2 ^ 53) := by norm_num
    nlinarith
  have hnorm := normal_of_value c hcn
  set a := Wasm.IEEE64.exponent c with ha
  have hfin : a ≠ 2047 := by
    have h := hcf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    exact h
  have hlt : a < 2048 := Nat.mod_lt _ (by norm_num)
  have ha1 : 1 ≤ a := hnorm.1
  set P : ℝ := (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1022 with hP
  have hPpos : 0 < P := by positivity
  have hcP : P ≤ value c := by
    rw [hP, ← zpow_eq a hnorm.1]
    exact value_ge_of_exponent c a ((a : Int) - 1023) hnorm.1 hlt (by ring) hnorm.2 le_rfl
  have hpow1 : (2 : ℝ) ^ a = 2 * (2 : ℝ) ^ (a - 1) := by
    rw [show a = (a - 1) + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have hc2P : value c < 2 * P := by
    have h := magnitude_lt c (a + 1) (((a + 1 : Nat) : Int) - 1023) (by omega) (by ring)
      (by omega)
    rw [zpow_eq (a + 1) (by omega), Nat.add_sub_cancel, hpow1] at h
    rw [hP]
    have h2 : 2 * (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1022 =
        2 * ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1022) := by ring
    rw [h2] at h
    exact lt_of_le_of_lt (le_abs_self _) h
  have hc63 : c.toNat < 2 ^ 63 := by
    have h := hnorm.2
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at h
    exact h
  have hbA : value (UInt64.ofNat (a * 2 ^ 52)) = P := boundary_pow a hnorm.1 hlt
  have hbB1 : value (UInt64.ofNat ((a + 1) * 2 ^ 52)) = 2 * P := by
    rw [boundary_pow (a + 1) (by omega) (by omega), Nat.add_sub_cancel, hpow1, hP]
    ring
  have hm52 : m + 1 ≤ 2 ^ 52 := by omega
  rcases le_or_gt P y with hPy | hyP
  · have hspace : (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074 = P / (2 : ℝ) ^ 52 := by
      rw [hP]
      field_simp
    have hy2P : y - k * y < 2 * P := by linarith
    have hmy : (m + 3 / 8 : ℝ) * y < (2 * m + 1) * P := by
      have h2 : (m + 1 / 2 : ℝ) * (y - k * y) < (m + 1 / 2) * (2 * P) :=
        mul_lt_mul_of_pos_left hy2P (by positivity)
      have h3 : (m + 3 / 8 : ℝ) * y ≤ (m + 1 / 2) * (y - k * y) := by nlinarith
      linarith
    have he : |value c - y| < (2 * m + 1) * ((2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ 1074) / 2 := by
      rw [hspace]
      calc |value c - y| ≤ k * y := hc
        _ = (m + 3 / 8 : ℝ) * y / 2 ^ 53 := by rw [hk, hu]; ring
        _ < (2 * m + 1) * P / 2 ^ 53 := by
            apply div_lt_div_of_pos_right hmy (by positivity)
        _ = (2 * m + 1) * (P / 2 ^ 52) / 2 := by ring
    rcases Nat.lt_or_ge (a + 2) 2047 with hb | hb
    · have hbB : value (UInt64.ofNat ((a + 2) * 2 ^ 52)) = 4 * P := by
        rw [boundary_pow (a + 2) (by omega) (by omega), hP,
          show a + 2 - 1 = (a - 1) + 2 by omega, pow_add]
        ring
      exact steps_binades m hm hm52 y c a (a + 2) (by omega) (by omega)
        (by rw [hbA]; exact hPy) (fun _ => by rw [hbB]; linarith) hc63 (by rw [hbA]; exact hcP)
        (by rw [hbB]; linarith) he
    · have hbB : value (UInt64.ofNat (2047 * 2 ^ 52)) = (2 : ℝ) ^ 1024 := by
        rw [boundary_pow 2047 (by norm_num) (by norm_num)]
        norm_num
      have hP1 : 2 * P ≤ (2 : ℝ) ^ 1024 := by
        have h1 : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ 2046 := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [hpow1] at h1
        rw [hP, mul_div_assoc', div_le_iff₀ (by positivity)]
        calc 2 * (2 : ℝ) ^ (a - 1) ≤ 2 ^ 2046 := h1
          _ = 2 ^ 1024 * 2 ^ 1022 := by norm_num
      exact steps_binades m hm hm52 y c a 2047 (by omega) le_rfl
        (by rw [hbA]; exact hPy) (fun h => absurd h (lt_irrefl _)) hc63
        (by rw [hbA]; exact hcP) (by rw [hbB]; linarith) he
  · have ha2 : 2 ≤ a := by
      by_contra h
      have ha1' : a = 1 := by omega
      have hP1 : P = 1 / (2 : ℝ) ^ 1022 := by rw [hP, ha1']; norm_num
      have : (1 : ℝ) / 2 ^ 1022 ≤ (17 / 16) / 2 ^ 1022 := by norm_num
      linarith
    have hspace : (2 : ℝ) ^ (a - 1 - 1) / (2 : ℝ) ^ 1074 = P / (2 : ℝ) ^ 53 := by
      rw [hP]
      have h2 : (2 : ℝ) ^ (a - 1) = 2 * (2 : ℝ) ^ (a - 1 - 1) := by
        rw [show a - 1 = (a - 1 - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      rw [h2]
      field_simp
    have he : |value c - y| < (2 * m + 1) * ((2 : ℝ) ^ (a - 1 - 1) / (2 : ℝ) ^ 1074) / 2 := by
      rw [hspace]
      have hmy : (m + 3 / 8 : ℝ) * y < (m + 1 / 2) * P := by
        have h1 : (m + 3 / 8 : ℝ) * y < (m + 3 / 8) * P := mul_lt_mul_of_pos_left hyP (by positivity)
        have h2 : (m + 3 / 8 : ℝ) * P ≤ (m + 1 / 2) * P := by nlinarith
        linarith
      calc |value c - y| ≤ k * y := hc
        _ = (m + 3 / 8 : ℝ) * y / 2 ^ 53 := by rw [hk, hu]; ring
        _ < (m + 1 / 2) * P / 2 ^ 53 := by
            apply div_lt_div_of_pos_right hmy (by positivity)
        _ = (2 * m + 1) * (P / 2 ^ 53) / 2 := by ring
    have hbA' : value (UInt64.ofNat ((a - 1) * 2 ^ 52)) = P / 2 := by
      rw [boundary_pow (a - 1) (by omega) (by omega), hP]
      have h2 : (2 : ℝ) ^ (a - 1) = 2 * (2 : ℝ) ^ (a - 1 - 1) := by
        rw [show a - 1 = (a - 1 - 1) + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring
      rw [h2]
      ring
    exact steps_binades m hm hm52 y c (a - 1) (a + 1) (by omega) (by omega)
      (by rw [hbA']; linarith) (fun _ => by rw [hbB1]; linarith) hc63
      (by rw [hbA']; linarith) (by rw [hbB1]; linarith) he

/-- A finite word within `m + 3/8` units of roundoff of `y`, relative to `|y|`, lies within `m`
steps of the signed nearest-even reference of `y`, for `1 ≤ m ≤ 64`. -/
theorem within_steps_relative (m : Nat) (hm : 1 ≤ m) (hm64 : m ≤ 64) (y : ℝ) (c : UInt64)
    (hcf : Finite c) (hy : (17 / 16) / (2 : ℝ) ^ 1022 ≤ |y|)
    (hc : |value c - y| ≤ (m + 3 / 8) * unitRoundoff64 * |y|) :
    F64SignedRounding.WithinSteps m y c := by
  have hu : unitRoundoff64 = 1 / (2 : ℝ) ^ 53 := rfl
  have hmr64 : (m : ℝ) ≤ 64 := by exact_mod_cast hm64
  have hk : (m + 3 / 8 : ℝ) * unitRoundoff64 ≤ 1 / 2 := by
    rw [hu]
    have : (m + 3 / 8 : ℝ) * (1 / 2 ^ 53) ≤ 65 * (1 / 2 ^ 53) := by gcongr; linarith
    linarith [show (65 : ℝ) * (1 / 2 ^ 53) ≤ 1 / 2 by norm_num]
  rcases lt_or_ge y 0 with hneg | hpos
  · rw [abs_of_neg hneg] at hy hc
    have hcl := (abs_le.mp hc).2
    have hcn : value c < 0 := by
      have hy0 : 0 < -y := by linarith [show (0 : ℝ) < (17 / 16) / 2 ^ 1022 by positivity]
      nlinarith
    have hmag : 0 < Wasm.IEEE64.scaledMagnitude c := by
      rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude c) with h | h
      · exfalso
        have hz : value c = 0 := by
          simp only [value, Wasm.IEEE64.scaledValue, h]
          split <;> simp
        linarith
      · exact h
    have hs : Wasm.IEEE64.sign c = true := (sign_value c hmag).mpr hcn
    obtain ⟨hnf, hnv⟩ := negate_value c hcf
    have hns : Wasm.IEEE64.sign (Wasm.IEEE64.negate c) = false := by
      have h := (F64Sign.fields_negate c).2.2
      rw [hs] at h
      exact h
    have hstep := steps_relative m hm hm64 (-y) (Wasm.IEEE64.negate c) hnf hy (by
      rw [hnv, show -value c - -y = -(value c - y) by ring, abs_neg]
      exact hc)
    have h := F64SignedRounding.within_of_neg m y hneg (Wasm.IEEE64.negate c)
      (lt_limit_of_finite _ hnf hns).le hstep.1 hstep.2
    rwa [F64RelativeStep.negate_negate] at h
  · have hy0 : 0 < y := by
      rw [abs_of_nonneg hpos] at hy
      exact lt_of_lt_of_le (by positivity) hy
    rw [abs_of_pos hy0] at hy hc
    have hcl := (abs_le.mp hc).1
    have hcp : 0 < value c := by nlinarith
    have hs : Wasm.IEEE64.sign c = false := by
      have hmag : 0 < Wasm.IEEE64.scaledMagnitude c := by
        rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude c) with h | h
        · exfalso
          have hz : value c = 0 := by
            simp only [value, Wasm.IEEE64.scaledValue, h]
            split <;> simp
          linarith
        · exact h
      cases h : Wasm.IEEE64.sign c
      · rfl
      · exact absurd ((sign_value c hmag).mp h) (not_lt.mpr hcp.le)
    have hstep := steps_relative m hm hm64 y c hcf hy hc
    exact F64SignedRounding.within_of_nonneg m y hy0.le c (lt_limit_of_finite c hcf hs).le
      hstep.1 hstep.2


/-- A nonnegative finite word within `(2 m + 1)/2 · 2^-1074` of a nonnegative `y` lies within `m`
steps of the reference of `y`. -/
theorem within_steps_low (m : Nat) (hm : 1 ≤ m) (hm52 : m + 1 ≤ 2 ^ 52) (y : ℝ) (hy : 0 ≤ y)
    (c : UInt64) (hcf : Finite c) (hcs : Wasm.IEEE64.sign c = false)
    (he : |value c - y| < (2 * m + 1) * (1 / (2 : ℝ) ^ 1074) / 2) :
    F64SignedRounding.WithinSteps m y c := by
  have hlim : limit < 2 ^ 63 := by decide
  have hcl := lt_limit_of_finite c hcf hcs
  have h0 : value (UInt64.ofNat 0) = 0 := by
    simp [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.sign,
      Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
  have hstep := steps_full m hm hm52 y (1 / (2 : ℝ) ^ 1074) c 0 limit (by positivity)
    (by norm_num) (by decide) le_rfl ⟨Nat.zero_le _, hcl.le⟩ (by rw [h0]; exact hy)
    (fun h => absurd h (lt_irrefl _)) (fun n _ hn => by
      have h := F64FullStep.gap_lower n 0 (by simp) (by omega)
      simpa using h) he
  exact F64SignedRounding.within_of_nonneg m y hy c hcl.le hstep.1 hstep.2

#print axioms gap_sum
#print axioms steps_of_spacing_le
#print axioms steps_full
#print axioms steps_binades
#print axioms steps_relative
#print axioms within_steps_relative
#print axioms within_steps_low

end LeanExe.ProofKit.F64RelativeSteps
