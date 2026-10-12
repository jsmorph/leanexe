import LeanExe.ProofKit.F64FullStep
import LeanExe.ProofKit.F64Approx
import LeanExe.ProofKit.F64RoundNearest

/-!
Two steps from a total error: a nonnegative word within two and a half spacings of a real number
lies within two representable steps of the number's nearest-even reference.  The proofs follow
`F64FullStep.one_step_of_spacing_le`, `one_step_full`, and `one_step_binades`, with one more word
between the reference and the word.
-/

namespace LeanExe.ProofKit.F64TwoSteps
open CodeLib.IEEE64 F64NearestNonnegative F64PositiveOrder F64NearestStep F64FullStep
  F64RoundNearest

set_option exponentiation.threshold 4096

theorem two_steps_of_spacing_le (y d : ℝ) (c w : UInt64) (L U : Nat)
    (hd : 0 < d) (hU : U ≤ limit)
    (hc : L ≤ c.toNat ∧ c.toNat ≤ U)
    (hw : Nearest y w) (hwr : L ≤ w.toNat ∧ w.toNat ≤ U)
    (hspacing : ∀ n : Nat, L ≤ n → n < U →
      d ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n))
    (he : |value c - y| < 5 * d / 2) :
    c.toNat ≤ w.toNat + 2 ∧ w.toNat ≤ c.toNat + 2 := by
  have hlim : limit < 2 ^ 63 := by decide
  have hwl := hw.1
  have word_nat (n : Nat) (hn : n ≤ U) : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (lt_trans (lt_of_le_of_lt (hn.trans hU) hlim) (by norm_num))
  have hc63 : c.toNat < 2 ^ 63 := lt_of_le_of_lt (hc.2.trans hU) hlim
  constructor
  · by_contra h
    have hw1 : w.toNat + 1 ≤ U := by omega
    have hw3 : w.toNat + 3 ≤ U := by omega
    have hg1 := hspacing w.toNat hwr.1 (by omega)
    have hg2 := hspacing (w.toNat + 1) (by omega) (by omega)
    have hg3 := hspacing (w.toNat + 2) (by omega) (by omega)
    simp only [UInt64.ofNat_toNat] at hg1
    have hv : value w < value (UInt64.ofNat (w.toNat + 1)) := by linarith
    have hn : (UInt64.ofNat (w.toNat + 1)).toNat < limit := by
      rw [word_nat _ hw1]
      omega
    have hm := upper_midpoint _ _ y hv (hw.2 _ hn)
    have hc3 : value (UInt64.ofNat (w.toNat + 3)) ≤ value c := by
      apply (value_le_iff (by rw [word_nat _ hw3]; omega) hc63).mpr
      rw [word_nat _ hw3]
      omega
    have he' := (le_abs_self (value c - y)).trans_lt he
    norm_num only [Nat.add_assoc, Nat.reduceAdd] at hg2 hg3
    linarith
  · by_contra h
    have hmL : L ≤ w.toNat - 1 := by omega
    have hpL : L ≤ w.toNat - 2 := by omega
    have hqL : L ≤ w.toNat - 3 := by omega
    have hmU : w.toNat - 1 ≤ U := by omega
    have hqU : w.toNat - 3 ≤ U := by omega
    have hg1 := hspacing (w.toNat - 1) hmL (by omega)
    have hg2 := hspacing (w.toNat - 2) hpL (by omega)
    have hg3 := hspacing (w.toNat - 3) hqL (by omega)
    have hmadd : w.toNat - 1 + 1 = w.toNat := by omega
    have hpadd : w.toNat - 2 + 1 = w.toNat - 1 := by omega
    have hqadd : w.toNat - 3 + 1 = w.toNat - 2 := by omega
    rw [hmadd, UInt64.ofNat_toNat] at hg1
    rw [hpadd] at hg2
    rw [hqadd] at hg3
    have hv : value (UInt64.ofNat (w.toNat - 1)) < value w := by linarith
    have hn : (UInt64.ofNat (w.toNat - 1)).toNat < limit := by
      rw [word_nat _ hmU]
      omega
    have hm := lower_midpoint _ _ y hv (hw.2 _ hn)
    have hc3 : value c ≤ value (UInt64.ofNat (w.toNat - 3)) := by
      apply (value_le_iff hc63 (by rw [word_nat _ hqU]; omega)).mpr
      rw [word_nat _ hqU]
      omega
    have he' := (neg_le_abs (value c - y)).trans_lt he
    linarith

/-- `F64FullStep.one_step_full` with two steps for an error below two and a half spacings. -/
theorem two_steps_full (y d : ℝ) (c : UInt64) (L U : Nat)
    (hd : 0 < d) (hdtop : d ≤ (2 : ℝ) ^ 970)
    (hL : L < limit) (hU : U ≤ limit)
    (hc : L ≤ c.toNat ∧ c.toNat ≤ U)
    (hyL : value (UInt64.ofNat L) ≤ y)
    (hyU : U < limit → y ≤ value (UInt64.ofNat U))
    (hspacing : ∀ n : Nat, L ≤ n → n < U →
      d ≤ value (UInt64.ofNat (n + 1)) - value (UInt64.ofNat n))
    (he : |value c - y| < 5 * d / 2) :
    c.toNat ≤ (F64PositiveRounding.roundNearestEven y).toNat + 2 ∧
      (F64PositiveRounding.roundNearestEven y).toNat ≤ c.toNat + 2 := by
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
    exact two_steps_of_spacing_le y d c _ L U hd hU hc hw ⟨hwL, hwU⟩ hspacing he

/-- Two steps from a total error below two and a half spacings of binade `n`, for a word and a
positive `y` at or above the start of that binade. -/
theorem within_two_of_error (y : ℝ) (c : UInt64) (n : ℕ) (hn1 : 1 ≤ n) (hn : n < 2046) (E : ℝ)
    (hcf : Finite c) (hc : |value c - y| ≤ E)
    (hy : value (UInt64.ofNat (n * 2 ^ 52)) + E ≤ y)
    (hE : E < 5 * ((2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ 1074) / 2) :
    F64SignedRounding.WithinSteps 2 y c := by
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hc
  have hB := F64PositiveSpacing.boundary_value n hn1 (by omega)
  have hB0 : 0 < value (UInt64.ofNat (n * 2 ^ 52)) := by rw [hB]; positivity
  have hyB : value (UInt64.ofNat (n * 2 ^ 52)) ≤ y := by linarith
  have hcl : value (UInt64.ofNat (n * 2 ^ 52)) ≤ value c := by
    have := (abs_le.mp hc).1
    linarith
  have hcpos : 0 < value c := by linarith
  have hmagpos : 0 < Wasm.IEEE64.scaledMagnitude c := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude c) with h0 | h0
    · have : value c = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h0]
        split <;> simp
      linarith
    · exact h0
  have hsign : Wasm.IEEE64.sign c = false := by
    cases hs : Wasm.IEEE64.sign c
    · rfl
    · have := (F64Magnitude.sign_value c hmagpos).mp hs
      linarith
  have hlim := F64Magnitude.lt_limit_of_finite c hcf hsign
  have hc63 : c.toNat < 2 ^ 63 := hlim.trans (by decide)
  have hl : limit = 2047 * 2 ^ 52 := rfl
  have hnw : (UInt64.ofNat (n * 2 ^ 52)).toNat = n * 2 ^ 52 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hcL : n * 2 ^ 52 ≤ c.toNat := by
    have h := (value_le_iff (by rw [hnw]; omega) hc63).mp hcl
    rwa [hnw] at h
  have hstep := two_steps_full y ((2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ 1074) c (n * 2 ^ 52) limit
    (by positivity) (by
      calc (2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ 1074 ≤ (2 : ℝ) ^ 2044 / (2 : ℝ) ^ 1074 := by
            gcongr
            all_goals first | omega | norm_num
        _ = (2 : ℝ) ^ 970 := by norm_num)
    (by rw [hl]; omega) le_rfl ⟨hcL, hlim.le⟩ hyB (fun h => absurd h (lt_irrefl _))
    (fun m hm1 hm2 => gap_lower m n hm1 (by rw [hl] at hm2; omega)) (lt_of_le_of_lt hc hE)
  exact F64SignedRounding.within_of_nonneg 2 y (by linarith) c hlim.le hstep.1 hstep.2

theorem steps_two_of_nearest (S y : ℝ) (w r : UInt64) (hw : Nearest S w) (hr : Nearest y r)
    (a : ℕ) (ha : a < 2047) (hS : value (UInt64.ofNat (a * 2 ^ 52)) ≤ S)
    (hy : value (UInt64.ofNat (a * 2 ^ 52)) ≤ y)
    (h : |S - y| < 2 * ((2 : ℝ) ^ (a - 1) / 2 ^ 1074)) :
    w.toNat ≤ r.toNat + 2 ∧ r.toNat ≤ w.toNat + 2 := by
  have hlim : limit = 2047 * 2 ^ 52 := rfl
  have hwa := nearest_above S w hw a ha hS
  have hra := nearest_above y r hr a ha hy
  have hw1 := hw.1
  have hr1 := hr.1
  have word (n : ℕ) (hn : n < 2 ^ 63) : (UInt64.ofNat n).toNat = n :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have habs := abs_lt.mp h
  have habs_l := habs.1
  have habs_r := habs.2
  constructor
  · by_contra hc
    push Not at hc
    have g1 := F64FullStep.gap_lower r.toNat a hra (by rw [hlim] at hw1; omega)
    have g2 := F64FullStep.gap_lower (r.toNat + 1) a (by omega) (by rw [hlim] at hw1; omega)
    have g3 := F64FullStep.gap_lower (r.toNat + 2) a (by omega) (by rw [hlim] at hw1; omega)
    simp only [UInt64.ofNat_toNat] at g1
    have hle : value (UInt64.ofNat (r.toNat + 2 + 1)) ≤ value w :=
      (F64PositiveOrder.value_le_iff (by rw [word _ (by rw [hlim] at hw1; omega)]; omega)
        (by rw [hlim] at hw1; omega)).mpr (by rw [word _ (by rw [hlim] at hw1; omega)]; omega)
    have hpos : (0 : ℝ) < 2 ^ (a - 1) / 2 ^ 1074 := by positivity
    have hpw : value (UInt64.ofNat (r.toNat + 2)) < value w := by linarith
    have hm1 := F64NearestStep.lower_midpoint (value w) (value (UInt64.ofNat (r.toNat + 2))) S
      hpw (hw.2 _ (by rw [word _ (by rw [hlim] at hw1; omega), hlim]; omega))
    have hm2 := F64NearestStep.upper_midpoint (value r) (value (UInt64.ofNat (r.toNat + 1))) y
      (by linarith) (hr.2 _ (by rw [word _ (by rw [hlim] at hw1; omega), hlim]; omega))
    norm_num only [Nat.add_assoc, Nat.reduceAdd] at g2 g3
    linarith
  · by_contra hc
    push Not at hc
    have g1 := F64FullStep.gap_lower w.toNat a hwa (by rw [hlim] at hr1; omega)
    have g2 := F64FullStep.gap_lower (w.toNat + 1) a (by omega) (by rw [hlim] at hr1; omega)
    have g3 := F64FullStep.gap_lower (w.toNat + 2) a (by omega) (by rw [hlim] at hr1; omega)
    simp only [UInt64.ofNat_toNat] at g1
    have hle : value (UInt64.ofNat (w.toNat + 2 + 1)) ≤ value r :=
      (F64PositiveOrder.value_le_iff (by rw [word _ (by rw [hlim] at hr1; omega)]; omega)
        (by rw [hlim] at hr1; omega)).mpr (by rw [word _ (by rw [hlim] at hr1; omega)]; omega)
    have hpos : (0 : ℝ) < 2 ^ (a - 1) / 2 ^ 1074 := by positivity
    have hpr : value (UInt64.ofNat (w.toNat + 2)) < value r := by linarith
    have hm1 := F64NearestStep.lower_midpoint (value r) (value (UInt64.ofNat (w.toNat + 2))) y
      hpr (hr.2 _ (by rw [word _ (by rw [hlim] at hr1; omega), hlim]; omega))
    have hm2 := F64NearestStep.upper_midpoint (value w) (value (UInt64.ofNat (w.toNat + 1))) S
      (by linarith) (hw.2 _ (by rw [word _ (by rw [hlim] at hr1; omega), hlim]; omega))
    norm_num only [Nat.add_assoc, Nat.reduceAdd] at g2 g3
    linarith

/-- Two steps for a rounded word whose exact value lies within two spacings of binade `a` from
`y`, both at or above the start of that binade in magnitude. -/
theorem within_two_of_rounded (c : UInt64) (S y : ℝ) (hc : Rounded c S) (a : ℕ) (ha1 : 1 ≤ a)
    (ha : a < 2047) (hS : value (UInt64.ofNat (a * 2 ^ 52)) ≤ |S|)
    (hy : value (UInt64.ofNat (a * 2 ^ 52)) ≤ |y|)
    (h : |S - y| < 2 * ((2 : ℝ) ^ (a - 1) / 2 ^ 1074)) (hyt : |y| < 2 ^ 1023) :
    F64SignedRounding.WithinSteps 2 y c := by
  obtain ⟨hcf, hneg, hpos, hnear⟩ := hc
  have hB := F64PositiveSpacing.boundary_value a ha1 (by omega)
  have hBh : (2 : ℝ) ^ (a - 1) / 2 ^ 1074 < value (UInt64.ofNat (a * 2 ^ 52)) := by
    rw [hB]
    apply div_lt_div_of_pos_right _ (by positivity)
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  have hB0 : 0 < value (UInt64.ofNat (a * 2 ^ 52)) := lt_of_le_of_lt (by positivity) hBh
  have hlim : limit = 2047 * 2 ^ 52 := rfl
  have hcl : (Wasm.IEEE64.abs c).toNat < limit := by
    rw [F64UpperWord.abs_toNat, hlim]
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
      ne_eq] at hcf
    have := c.toNat_lt
    omega
  have hN : Nearest |S| (Wasm.IEEE64.abs c) := by
    refine ⟨hcl, fun v hv => ?_⟩
    have h1 := hnear v
    rw [F64UpperWord.value_abs]
    rw [abs_of_nonneg (value_nonneg_of_lt v (by rw [hlim] at hv; omega))] at h1
    exact h1
  have hyo : |y| < F64PositiveRounding.overflowThreshold := by
    have : F64PositiveRounding.overflowThreshold = (2 : ℝ) ^ 1024 - (2 : ℝ) ^ 970 := rfl
    rw [this]
    have : (2 : ℝ) ^ 1023 ≤ 2 ^ 1024 - 2 ^ 970 := by norm_num
    linarith
  have hr := F64PositiveRounding.reference_finite |y| hyo
  have hrN : Nearest |y| (F64PositiveRounding.roundNearestEven |y|) := by
    rw [hr]
    exact (F64NearestEven.roundNearestEven_spec |y|).1
  have hhS : abs (|S| - |y|) < 2 * ((2 : ℝ) ^ (a - 1) / 2 ^ 1074) :=
    lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub S y) h
  have hst := steps_two_of_nearest |S| |y| _ _ hN hrN a ha hS hy hhS
  have hrle := F64SignedRounding.positive_reference_le |y|
  have hctn := F64UpperWord.abs_toNat c
  rcases lt_or_gt_of_ne (show y ≠ 0 by intro h0; rw [h0, abs_zero] at hy; linarith) with hy0 | hy0
  · -- negative: `S` is negative too
    have hS0 : S < 0 := by
      by_contra hc
      push Not at hc
      rw [abs_of_nonneg hc] at hS
      rw [abs_of_neg hy0] at hy
      obtain ⟨hab_l, hab_r⟩ := abs_lt.mp h
      set B := value (UInt64.ofNat (a * 2 ^ 52))
      set hh := (2 : ℝ) ^ (a - 1) / 2 ^ 1074
      have hBh2 : 2 * hh < 2 * B := by linarith
      linarith
    have hsc := hneg hS0
    have hct : 2 ^ 63 ≤ c.toNat := by
      simpa only [Wasm.IEEE64.sign, decide_eq_true_eq] using hsc
    have hneq : Wasm.IEEE64.negate (Wasm.IEEE64.abs c) = c := by
      apply UInt64.toNat_inj.mp
      rw [F64SignedRounding.negate_toNat]
      have hsa : Wasm.IEEE64.sign (Wasm.IEEE64.abs c) = false := by
        simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le, hctn]
        omega
      rw [hsa, if_neg (by simp), hctn]
      have := c.toNat_lt
      omega
    rw [← hneq]
    rw [abs_of_neg hy0] at hst hrle
    exact F64SignedRounding.within_of_neg 2 y hy0 _ (by rw [hlim] at hcl; omega) hst.1 hst.2
  · have hS0 : 0 < S := by
      by_contra hc
      push Not at hc
      rw [abs_of_nonpos hc] at hS
      rw [abs_of_pos hy0] at hy
      obtain ⟨hab_l, hab_r⟩ := abs_lt.mp h
      set B := value (UInt64.ofNat (a * 2 ^ 52))
      set hh := (2 : ℝ) ^ (a - 1) / 2 ^ 1074
      have hBh2 : 2 * hh < 2 * B := by linarith
      linarith
    have hsc := hpos hS0
    have hct : c.toNat < 2 ^ 63 := by
      simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hsc
    have heq : Wasm.IEEE64.abs c = c := by
      apply UInt64.toNat_inj.mp
      rw [hctn]
      omega
    rw [heq] at hst hcl
    rw [abs_of_pos hy0] at hst
    exact F64SignedRounding.within_of_nonneg 2 y hy0.le c (by rw [hlim] at hcl; omega)
      hst.1 hst.2

/-- Two steps relative to the input's binade: `X` lies in binade `n ≥ 2`, `y` between `(1 - κ) X`
and `X`, and the result within `ρ X` of `y`, with `ρ ≤ (5/2) 2 ^ -53 (1 - κ - ρ)`. -/
theorem within_two_rel (y : ℝ) (c : UInt64) (X : ℝ) (n : ℕ) (hn2 : 2 ≤ n) (hn : n < 2046)
    (hX : value (UInt64.ofNat (n * 2 ^ 52)) ≤ X)
    (hX2 : X < 2 * value (UInt64.ofNat (n * 2 ^ 52))) (κ ρ : ℝ) (hκ0 : 0 ≤ κ) (hρ0 : 0 ≤ ρ)
    (hcf : Finite c) (hc : |value c - y| ≤ ρ * X) (hyl : (1 - κ) * X ≤ y)
    (hρ : ρ ≤ 5 / 2 / 2 ^ 53 * (1 - κ - ρ)) (hκ : κ + ρ < 1 / 3) :
    F64SignedRounding.WithinSteps 2 y c := by
  have hB := F64PositiveSpacing.boundary_value n (by omega) (by omega)
  set B := value (UInt64.ofNat (n * 2 ^ 52)) with hBdef
  have hB0 : 0 < B := by rw [hB]; positivity
  have hX0 : 0 < X := lt_of_lt_of_le hB0 hX
  have hρlt : ρ < 5 / 2 / 2 ^ 53 := by
    rcases eq_or_lt_of_le hρ0 with h | h
    · rw [← h]
      positivity
    · nlinarith
  have hρX : ρ * X ≤ 2 * ρ * B := by nlinarith
  have hsp : (2 : ℝ) ^ (n - 1) / (2 : ℝ) ^ 1074 = B / 2 ^ 52 := by
    rw [hB, show n + 51 = (n - 1) + 52 by omega, pow_add]
    field_simp
  by_cases hhi : B + ρ * X ≤ y
  · refine within_two_of_error y c n (by omega) (by omega) (ρ * X) hcf hc hhi ?_
    rw [hsp]
    have : 2 * ρ * B < 2 * (5 / 2 / 2 ^ 53) * B := by nlinarith
    have h5 : 2 * (5 / 2 / 2 ^ 53) * B = 5 * (B / 2 ^ 52) / 2 := by ring
    linarith
  · have hn0 : n - 1 < 2047 := by omega
    have hBl : value (UInt64.ofNat ((n - 1) * 2 ^ 52)) = B / 2 := by
      rw [F64PositiveSpacing.boundary_value (n - 1) (by omega) (by omega), hB,
        show n + 51 = (n - 1 + 51) + 1 by omega, pow_succ]
      ring
    have hsp' : (2 : ℝ) ^ (n - 1 - 1) / (2 : ℝ) ^ 1074 = B / 2 ^ 53 := by
      rw [hB, show n + 51 = (n - 1 - 1) + 53 by omega, pow_add]
      field_simp
    have hy' : y < B + ρ * X := lt_of_not_ge hhi
    have hk : 0 < 1 - κ - ρ := by linarith
    have hXB : X * (1 - κ - ρ) < B := by nlinarith
    have hρX' : ρ * X ≤ 5 / 2 / 2 ^ 53 * (X * (1 - κ - ρ)) := by
      have := mul_le_mul_of_nonneg_right hρ hX0.le
      linarith
    have hlow : (1 - κ) * B ≤ (1 - κ) * X := by
      apply mul_le_mul_of_nonneg_left hX
      linarith
    refine within_two_of_error y c (n - 1) (by omega) (by omega) (ρ * X) hcf hc ?_ ?_
    · rw [hBl]
      have : 2 * ρ * B ≤ (1 / 2 - κ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0.le
        linarith
      linarith
    · rw [hsp']
      have : 5 / 2 / 2 ^ 53 * (X * (1 - κ - ρ)) < 5 / 2 / 2 ^ 53 * B := by
        apply mul_lt_mul_of_pos_left hXB
        positivity
      have h5 : 5 / 2 / 2 ^ 53 * B = 5 * (B / 2 ^ 53) / 2 := by ring
      linarith

/-- Two steps below `2 ^ -1020`, where consecutive words lie at least `2 ^ -1074` apart, for a
nonnegative word and a nonnegative `y`. -/
theorem within_two_low (y : ℝ) (c : UInt64) (hcf : Finite c) (hc63 : c.toNat < 2 ^ 63)
    (hc1 : value c ≤ 1 / 2 ^ 1020) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2 ^ 1020)
    (hE : |value c - y| < 5 / 2 / 2 ^ 1074) :
    F64SignedRounding.WithinSteps 2 y c := by
  have hl : limit = 2047 * 2 ^ 52 := rfl
  have hUw : (UInt64.ofNat (3 * 2 ^ 52)).toNat = 3 * 2 ^ 52 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hUv : value (UInt64.ofNat (3 * 2 ^ 52)) = 1 / 2 ^ 1020 := by
    rw [F64PositiveSpacing.boundary_value 3 (by norm_num) (by norm_num)]
    norm_num
  have hcU : c.toNat ≤ 3 * 2 ^ 52 := by
    have h := (value_le_iff hc63 (by rw [hUw]; norm_num)).mp (by rw [hUv]; exact hc1)
    rwa [hUw] at h
  have h0 : value (UInt64.ofNat 0) = 0 := by
    have h : Wasm.IEEE64.scaledValue (UInt64.ofNat 0) = 0 := by decide +kernel
    rw [value, h]
    norm_num
  have hd : ((2 : ℝ) ^ (0 - 1) / 2 ^ 1074) = 1 / 2 ^ 1074 := by norm_num
  have hstep := two_steps_full y ((2 : ℝ) ^ (0 - 1) / 2 ^ 1074) c 0 (3 * 2 ^ 52)
    (by positivity) (by rw [hd]; norm_num) (by rw [hl]; norm_num) (by rw [hl]; norm_num)
    ⟨Nat.zero_le _, hcU⟩ (by rw [h0]; exact hy0) (fun _ => by rw [hUv]; exact hy1)
    (fun m _ hm2 => gap_lower m 0 (by omega) (by omega)) (by rw [hd]; linarith)
  exact F64SignedRounding.within_of_nonneg 2 y hy0 c (by omega) hstep.1 hstep.2

#print axioms within_two_of_error
#print axioms within_two_low
#print axioms steps_two_of_nearest
#print axioms within_two_of_rounded
#print axioms within_two_rel

end LeanExe.ProofKit.F64TwoSteps
