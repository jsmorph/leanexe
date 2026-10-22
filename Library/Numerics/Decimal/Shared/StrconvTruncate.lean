import Library.Numerics.Decimal.Shared.StrconvWords

/-!
Keeping the first 768 significant digits of a decimal (113 for binary32) and replacing a nonzero
remainder by half a unit in the last kept place does not change the rounding.  The decision points
of the rounding of a binade `E` are its half-grid points `k · 2 ^ (E - 1) / 2` in units of the
least subnormal (`halfPoint`): the ends of the binade, the midpoints between neighbors, and the
overflow threshold.  `refPos_transfer` shows that two reals in an open interval that holds no
half-grid point of the binades 1 to `F - 1` have the same reference.  For binary64 every such point,
divided by `2 ^ 1074`, is `c · 10 ^ i` with `c < 10 ^ 768` (`halfPoint_decimal64`): it is
`k · 2 ^ (E - 1076)`, an integer below `10 ^ 309` when `E ≥ 1076` and `k · 5 ^ s / 10 ^ s` with
`s = 1076 - E ≤ 1075` otherwise, and `(2 ^ 54 + 1) · 5 ^ 1075 < 10 ^ 768`.  A number `c · 10 ^ i`
with `c < 10 ^ K` cannot lie strictly between `D · 10 ^ j` and `(D + 1) · 10 ^ j` when
`D ≥ 10 ^ (K - 1)` (`not_between`), so the open interval of the dropped digits holds no decision
point (`truncate64`, `truncate32`).  The argument is the one of the research report, section 2.5.
-/

namespace Library.Numerics.Decimal.Shared.StrconvTruncate
open StrconvGrid

set_option exponentiation.threshold 4096

/-- The half-grid point `k` of binade `E`, in units of the least subnormal. -/
noncomputable def halfPoint (E k : ℕ) : ℝ := (k : ℝ) * 2 ^ (E - 1) / 2

/-- Two reals in an open interval free of half-grid points of the binades 1 to `F - 1` have the
same reference. -/
theorem refPos_transfer (f : Fmt) (A B y y' : ℝ) (hA : 0 ≤ A) (hy1 : A < y) (hy2 : y < B)
    (hy1' : A < y') (hy2' : y' < B)
    (H : ∀ E k, 1 ≤ E → E ≤ f.F - 1 → k ≤ 2 ^ (f.p + 1) + 1 →
      ¬ (A < halfPoint E k ∧ halfPoint E k < B)) :
    refPos f y = refPos f y' := by
  have hF := f.hF
  have hp := f.hp
  -- a half-grid point lies below both or above both
  have side : ∀ E k, 1 ≤ E → E ≤ f.F - 1 → k ≤ 2 ^ (f.p + 1) + 1 →
      (halfPoint E k ≤ A) ∨ (B ≤ halfPoint E k) := by
    intro E k h1 h2 h3
    by_contra hc
    push Not at hc
    exact H E k h1 h2 h3 hc
  have hT : threshold f = halfPoint (f.F - 1) (2 ^ (f.p + 1) - 1) := by
    unfold threshold halfPoint
    rw [show f.F - 1 - 1 = (f.F - 3) + 1 by omega, pow_succ]
    push_cast [Nat.one_le_two_pow]
    ring
  rcases side (f.F - 1) (2 ^ (f.p + 1) - 1) (by omega) le_rfl
      (le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)) with h | h
  · -- both at or beyond the threshold
    rw [← hT] at h
    unfold refPos
    rw [if_pos (by linarith), if_pos (by linarith)]
  · rw [← hT] at h
    have hyT : y < threshold f := by linarith
    obtain ⟨E, Q, hR⟩ := exists_roundsTo f y (by linarith)
    obtain ⟨hQ, hQ1⟩ := significand_bounds f y E Q hR
    obtain ⟨hE, hb1, hb2, hr1, hr2, htie⟩ := hR
    -- the binade lies below the infinities
    have hEF : E ≤ f.F - 1 := by
      by_contra hc
      push Not at hc
      rcases hb2 with h2 | h2
      · omega
      · have : threshold f ≤ (2 : ℝ) ^ (f.p - 1) * 2 ^ (E - 1) := by
          rw [threshold_eq]
          have h4 : (4 * half f - 1 : ℝ) ≤ 2 ^ (f.p - 1) * 4 := by
            unfold half; push_cast; linarith [pow_pos (by norm_num : (0 : ℝ) < 2) (f.p - 1)]
          have h5 : (2 : ℝ) ^ (f.F - 3) * 4 ≤ 2 ^ (E - 1) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
            exact pow_le_pow_right₀ (by norm_num) (by omega)
          have h6 : (0 : ℝ) ≤ 2 ^ (f.F - 3) := by positivity
          have h7 : (0 : ℝ) ≤ 4 * half f - 1 := by
            have : (1 : ℝ) ≤ half f := by exact_mod_cast half_pos f
            linarith
          nlinarith
        linarith
    have sideE := fun k (hk : k ≤ 2 ^ (f.p + 1) + 1) => side E k hE hEF hk
    set S : ℝ := 2 ^ (E - 1) with hS
    have hS0 : 0 < S := by positivity
    have hP : ∀ k : ℕ, halfPoint E k = k * S / 2 := fun k => rfl
    -- the comparisons of `y` and `y'` with each half-grid point agree
    have lt_iff : ∀ k, k ≤ 2 ^ (f.p + 1) + 1 → (y < halfPoint E k ↔ y' < halfPoint E k) := by
      intro k hk
      rcases sideE k hk with h1 | h1
      · constructor <;> intro <;> linarith
      · constructor <;> intro <;> linarith
    have ne1 : ∀ k, k ≤ 2 ^ (f.p + 1) + 1 → y ≠ halfPoint E k := by
      intro k hk heq
      rcases sideE k hk with h1 | h1 <;> linarith
    have ne2 : ∀ k, k ≤ 2 ^ (f.p + 1) + 1 → y' ≠ halfPoint E k := by
      intro k hk heq
      rcases sideE k hk with h1 | h1 <;> linarith
    have hpow : (2 : ℝ) ^ f.p = 2 * 2 ^ (f.p - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hk1 : 2 ^ (f.p + 1) ≤ 2 ^ (f.p + 1) + 1 := by omega
    have hk2 : 2 ^ f.p ≤ 2 ^ (f.p + 1) + 1 := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ f.p); omega
    have hQk : 2 * Q + 1 ≤ 2 ^ (f.p + 1) + 1 := by
      unfold half at hQ
      rw [show f.p + 1 = (f.p - 1) + 2 by omega, pow_add]; omega
    have hR' : RoundsTo f y' E Q := by
      refine ⟨hE, ?_, ?_, ?_, ?_, ?_⟩
      · have e : (2 : ℝ) ^ f.p * S = halfPoint E (2 ^ (f.p + 1)) := by
          rw [hP]; push_cast; rw [pow_succ]; ring
        rw [e] at hb1 ⊢; exact (lt_iff _ hk1).mp hb1
      · rcases hb2 with h1 | h1
        · exact Or.inl h1
        · right
          have e : (2 : ℝ) ^ (f.p - 1) * S = halfPoint E (2 ^ f.p) := by
            rw [hP]; push_cast; rw [hpow]; ring
          rw [e] at h1 ⊢
          by_contra hc; push Not at hc
          exact (not_lt.mpr h1) ((lt_iff _ hk2).mpr hc)
      · have e : (2 * Q + 1 : ℝ) * S = 2 * halfPoint E (2 * Q + 1) := by rw [hP]; push_cast; ring
        rw [e] at hr1 ⊢
        have : y ≤ halfPoint E (2 * Q + 1) := by linarith
        have : y < halfPoint E (2 * Q + 1) := lt_of_le_of_ne this (ne1 _ hQk)
        have := (lt_iff _ hQk).mp this
        linarith
      · rcases Nat.eq_zero_or_pos Q with h0 | h0
        · subst h0
          have : 0 ≤ y' := by linarith
          simp; linarith
        · have hQk' : 2 * Q - 1 ≤ 2 ^ (f.p + 1) + 1 := by omega
          have e : 2 * (Q : ℝ) * S = 2 * halfPoint E (2 * Q - 1) + S := by
            rw [hP]; push_cast [Nat.one_le_iff_ne_zero.mpr (by omega : 2 * Q ≠ 0)]; ring
          rw [e] at hr2 ⊢
          have : halfPoint E (2 * Q - 1) ≤ y := by linarith
          have : halfPoint E (2 * Q - 1) < y := lt_of_le_of_ne this (ne1 _ hQk').symm
          have : ¬ y' < halfPoint E (2 * Q - 1) := fun h' => (not_lt.mpr this.le) ((lt_iff _ hQk').mpr h')
          linarith
      · intro ht
        exfalso
        rcases ht with ht | ht
        · apply ne2 _ hQk
          rw [hP]; push_cast; linarith
        · rcases Nat.eq_zero_or_pos Q with h0 | h0
          · subst h0; simp at ht; linarith
          · have hQk' : 2 * Q - 1 ≤ 2 ^ (f.p + 1) + 1 := by omega
            apply ne2 _ hQk'
            rw [hP]; push_cast [Nat.one_le_iff_ne_zero.mpr (by omega : 2 * Q ≠ 0)]; linarith
    rw [positive_reference f y E Q ⟨hE, hb1, hb2, hr1, hr2, htie⟩,
      positive_reference f y' E Q hR']

/-- A number `c · 10 ^ i` with `c < 10 ^ K` does not lie strictly between `D · 10 ^ j` and
`(D + 1) · 10 ^ j` when `D ≥ 10 ^ (K - 1)`. -/
theorem not_between (K c D : ℕ) (i j : ℤ) (hK : 1 ≤ K) (hc : c < 10 ^ K) (hD : 10 ^ (K - 1) ≤ D) :
    ¬ ((D : ℝ) * 10 ^ j < c * 10 ^ i ∧ (c : ℝ) * 10 ^ i < (D + 1) * 10 ^ j) := by
  rintro ⟨h1, h2⟩
  have h10 : (0 : ℝ) < 10 ^ j := by positivity
  rcases le_or_gt j i with hij | hij
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, i = j + n := ⟨(i - j).toNat, by omega⟩
    have e : (c : ℝ) * 10 ^ i = ((c * 10 ^ n : ℕ) : ℝ) * 10 ^ j := by
      rw [hn, zpow_add₀ (by norm_num), zpow_natCast]; push_cast; ring
    rw [e] at h1 h2
    have a1 : (D : ℝ) < ((c * 10 ^ n : ℕ) : ℝ) := lt_of_mul_lt_mul_right h1 h10.le
    have a2 : ((c * 10 ^ n : ℕ) : ℝ) < D + 1 := lt_of_mul_lt_mul_right h2 h10.le
    have b1 : D < c * 10 ^ n := by exact_mod_cast a1
    have b2 : c * 10 ^ n < D + 1 := by exact_mod_cast a2
    omega
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, j = i + 1 + n := ⟨(j - i - 1).toNat, by omega⟩
    have hc' : (c : ℝ) < 10 ^ K := by exact_mod_cast hc
    have hD' : (10 : ℝ) ^ (K - 1) ≤ D := by exact_mod_cast hD
    have e1 : (10 : ℝ) ^ j = 10 ^ i * 10 * 10 ^ n := by
      rw [hn, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_natCast, zpow_one]
    have e2 : (10 : ℝ) ^ K = 10 ^ (K - 1) * 10 := by
      rw [← pow_succ]; congr 1; omega
    have h10i : (0 : ℝ) < 10 ^ i := by positivity
    have hn1 : (1 : ℝ) ≤ 10 ^ n := one_le_pow₀ (by norm_num)
    rw [e1] at h1
    have h5 : (c : ℝ) * 10 ^ i < 10 ^ (K - 1) * 10 * 10 ^ i := by
      rw [← e2]; exact mul_lt_mul_of_pos_right hc' h10i
    have h6 : (10 : ℝ) ^ (K - 1) * 10 * 10 ^ i ≤ D * (10 ^ i * 10 * 10 ^ n) :=
      calc (10 : ℝ) ^ (K - 1) * 10 * 10 ^ i = 10 ^ (K - 1) * (10 ^ i * 10) := by ring
        _ ≤ D * (10 ^ i * 10) := mul_le_mul_of_nonneg_right hD' (by positivity)
        _ ≤ D * (10 ^ i * 10 * 10 ^ n) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hn1) (by positivity)
    linarith

/-- Every half-grid point of a finite binade of binary64, divided by `2 ^ 1074`, has at most 768
significant digits. -/
theorem halfPoint_decimal64 (E k : ℕ) (hE : 1 ≤ E) (hE' : E ≤ 2046) (hk : k ≤ 2 ^ 54 + 1) :
    ∃ (c : ℕ) (i : ℤ), c < 10 ^ 768 ∧ halfPoint E k / 2 ^ 1074 = c * 10 ^ i := by
  unfold halfPoint
  by_cases h : 1076 ≤ E
  · refine ⟨k * 2 ^ (E - 1076), 0, ?_, ?_⟩
    · calc k * 2 ^ (E - 1076) ≤ (2 ^ 54 + 1) * 2 ^ 970 :=
            Nat.mul_le_mul hk (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ < 10 ^ 768 := by norm_num
    · have e : (2 : ℝ) ^ (E - 1) = 2 ^ (E - 1076) * 2 * 2 ^ 1074 := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [e]; push_cast; field_simp
  · refine ⟨k * 5 ^ (1076 - E), -((1076 - E : ℕ) : ℤ), ?_, ?_⟩
    · calc k * 5 ^ (1076 - E) ≤ (2 ^ 54 + 1) * 5 ^ 1075 :=
            Nat.mul_le_mul hk (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ < 10 ^ 768 := by norm_num
    · rw [zpow_neg, zpow_natCast]
      have e : (2 : ℝ) * 2 ^ 1074 = 2 ^ (E - 1) * 2 ^ (1076 - E) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have e2 : (10 : ℝ) ^ (1076 - E) = 2 ^ (1076 - E) * 5 ^ (1076 - E) := by
        rw [← mul_pow]; norm_num
      rw [e2, div_div, e]
      have h1 : (2 : ℝ) ^ (E - 1) ≠ 0 := by positivity
      have h2 : (2 : ℝ) ^ (1076 - E) ≠ 0 := by positivity
      have h3 : (5 : ℝ) ^ (1076 - E) ≠ 0 := by positivity
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

/-- Every half-grid point of a finite binade of binary32, divided by `2 ^ 149`, has at most 113
significant digits. -/
theorem halfPoint_decimal32 (E k : ℕ) (hE : 1 ≤ E) (hE' : E ≤ 254) (hk : k ≤ 2 ^ 25 + 1) :
    ∃ (c : ℕ) (i : ℤ), c < 10 ^ 113 ∧ halfPoint E k / 2 ^ 149 = c * 10 ^ i := by
  unfold halfPoint
  by_cases h : 151 ≤ E
  · refine ⟨k * 2 ^ (E - 151), 0, ?_, ?_⟩
    · calc k * 2 ^ (E - 151) ≤ (2 ^ 25 + 1) * 2 ^ 103 :=
            Nat.mul_le_mul hk (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ < 10 ^ 113 := by norm_num
    · have e : (2 : ℝ) ^ (E - 1) = 2 ^ (E - 151) * 2 * 2 ^ 149 := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [e]; push_cast; field_simp
  · refine ⟨k * 5 ^ (151 - E), -((151 - E : ℕ) : ℤ), ?_, ?_⟩
    · calc k * 5 ^ (151 - E) ≤ (2 ^ 25 + 1) * 5 ^ 150 :=
            Nat.mul_le_mul hk (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ < 10 ^ 113 := by norm_num
    · rw [zpow_neg, zpow_natCast]
      have e : (2 : ℝ) * 2 ^ 149 = 2 ^ (E - 1) * 2 ^ (151 - E) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have e2 : (10 : ℝ) ^ (151 - E) = 2 ^ (151 - E) * 5 ^ (151 - E) := by
        rw [← mul_pow]; norm_num
      rw [e2, div_div, e]
      have h1 : (2 : ℝ) ^ (E - 1) ≠ 0 := by positivity
      have h2 : (2 : ℝ) ^ (151 - E) ≠ 0 := by positivity
      have h3 : (5 : ℝ) ^ (151 - E) ≠ 0 := by positivity
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

/-- Keeping 768 significant digits: a value strictly between `D · 10 ^ j` and `(D + 1) · 10 ^ j`
with `D ≥ 10 ^ 767` has the reference of `(D + 1/2) · 10 ^ j`. -/
theorem truncate64 (D : ℕ) (hD : 10 ^ 767 ≤ D) (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) (j : ℤ) :
    refPos b64 ((D + θ) * 10 ^ j * 2 ^ 1074) = refPos b64 ((D + 1 / 2) * 10 ^ j * 2 ^ 1074) := by
  have hu : (0 : ℝ) < 10 ^ j * 2 ^ 1074 := by positivity
  apply refPos_transfer b64 (D * (10 ^ j * 2 ^ 1074)) ((D + 1) * (10 ^ j * 2 ^ 1074))
  · positivity
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · intro E k hE hE' hk ⟨a1, a2⟩
    obtain ⟨c, i, hc, he⟩ := halfPoint_decimal64 E k hE (by simpa [b64] using hE')
      (by simpa [b64] using hk)
    have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
    have e : halfPoint E k = c * 10 ^ i * 2 ^ 1074 := by
      rw [← he]; field_simp
    rw [e] at a1 a2
    apply not_between 768 c D i j (by norm_num) hc hD
    constructor
    · have : (D : ℝ) * 10 ^ j * 2 ^ 1074 < c * 10 ^ i * 2 ^ 1074 := by linarith
      exact lt_of_mul_lt_mul_right this hp.le
    · have : (c : ℝ) * 10 ^ i * 2 ^ 1074 < (D + 1) * 10 ^ j * 2 ^ 1074 := by linarith
      exact lt_of_mul_lt_mul_right this hp.le

/-- Keeping 113 significant digits for binary32. -/
theorem truncate32 (D : ℕ) (hD : 10 ^ 112 ≤ D) (θ : ℝ) (h0 : 0 < θ) (h1 : θ < 1) (j : ℤ) :
    refPos b32 ((D + θ) * 10 ^ j * 2 ^ 149) = refPos b32 ((D + 1 / 2) * 10 ^ j * 2 ^ 149) := by
  have hu : (0 : ℝ) < 10 ^ j * 2 ^ 149 := by positivity
  apply refPos_transfer b32 (D * (10 ^ j * 2 ^ 149)) ((D + 1) * (10 ^ j * 2 ^ 149))
  · positivity
  · nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · intro E k hE hE' hk ⟨a1, a2⟩
    obtain ⟨c, i, hc, he⟩ := halfPoint_decimal32 E k hE (by simpa [b32] using hE')
      (by simpa [b32] using hk)
    have hp : (0 : ℝ) < 2 ^ 149 := by positivity
    have e : halfPoint E k = c * 10 ^ i * 2 ^ 149 := by
      rw [← he]; field_simp
    rw [e] at a1 a2
    apply not_between 113 c D i j (by norm_num) hc hD
    constructor
    · have : (D : ℝ) * 10 ^ j * 2 ^ 149 < c * 10 ^ i * 2 ^ 149 := by linarith
      exact lt_of_mul_lt_mul_right this hp.le
    · have : (c : ℝ) * 10 ^ i * 2 ^ 149 < (D + 1) * 10 ^ j * 2 ^ 149 := by linarith
      exact lt_of_mul_lt_mul_right this hp.le

#print axioms refPos_transfer
#print axioms not_between
#print axioms halfPoint_decimal64
#print axioms halfPoint_decimal32
#print axioms truncate64
#print axioms truncate32

end Library.Numerics.Decimal.Shared.StrconvTruncate
