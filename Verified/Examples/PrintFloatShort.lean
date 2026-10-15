import Verified.Examples.StrconvRound

/-!
The shortest decimals of an interval.  For an interval of positive reals from `lo` to `hi`, ends
included when `closed`, with `hi ≤ 3 lo`, let `J` be the largest exponent at which a multiple of
`10 ^ J` lies in the interval.  The multipliers `m` at `J` form a run of consecutive integers with
no multiple of 10, so they all have the same number `D` of digits (`same_digits`).  A decimal
`s · 10 ^ e` of the interval with `e < J` has more than `D` digits, except a one-digit `s` at
`e = J - 1` when `D = 1` (`more_digits`).  `shortest_of_choice` concludes that a decimal chosen as
the nearest among the multiples at `J`, or as a one-digit multiple at `J - 1` nearer than all of
them, has the fewest significant digits, the least distance among those, and an even last digit at
a tie, which is the order of `StrconvRound.Shortest64`.
-/

namespace Verified.Examples.PrintFloatShort
open StrconvRound

/-! ### Trailing zeros -/

theorem stripZerosFuel_mul (k d : ℕ) : ∃ z, d = stripZerosFuel k d * 10 ^ z := by
  induction k generalizing d with
  | zero => exact ⟨0, by simp [stripZerosFuel]⟩
  | succ k ih =>
    unfold stripZerosFuel
    split_ifs with h
    · obtain ⟨z, hz⟩ := ih (d / 10)
      refine ⟨z + 1, ?_⟩
      rw [pow_succ, ← mul_assoc, ← hz]
      have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.2)
      omega
    · exact ⟨0, by simp⟩

theorem stripZerosFuel_mod (k d : ℕ) (hd : 0 < d) (hk : d < 10 ^ k) :
    stripZerosFuel k d % 10 ≠ 0 := by
  induction k generalizing d with
  | zero => simp at hk; omega
  | succ k ih =>
    unfold stripZerosFuel
    split_ifs with h
    · apply ih (d / 10) (by omega)
      rw [pow_succ] at hk
      omega
    · intro h'; exact h ⟨by omega, h'⟩

theorem stripZeros_spec (d : ℕ) (hd : 0 < d) :
    0 < stripZeros d ∧ stripZeros d % 10 ≠ 0 ∧ ∃ z, d = stripZeros d * 10 ^ z := by
  obtain ⟨z, hz⟩ := stripZerosFuel_mul d d
  have hm := stripZerosFuel_mod d d hd (Nat.lt_pow_self (by norm_num))
  refine ⟨?_, hm, z, hz⟩
  rcases Nat.eq_zero_or_pos (stripZeros d) with h | h
  · unfold stripZeros at h; rw [h] at hz; simp at hz; omega
  · exact h

theorem stripZeros_self (d : ℕ) (hd : d % 10 ≠ 0) : stripZeros d = d := by
  unfold stripZeros
  obtain ⟨k, hk⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  rw [hk]
  unfold stripZerosFuel
  rw [ite_eq_right (by intro h; exact hd (by rw [hk]; exact h.2))]

/-! ### Numbers of digits -/

/-- The number of decimal digits; 0 for 0. -/
def nd (n : ℕ) : ℕ := (Nat.digits 10 n).length

theorem lt_pow_nd (n : ℕ) : n < 10 ^ nd n := Nat.lt_base_pow_length_digits (by norm_num)

theorem pow_nd_le (n : ℕ) (hn : n ≠ 0) : 10 ^ (nd n - 1) ≤ n := by
  have h : 10 ^ nd n ≤ 10 * n := Nat.base_pow_length_digits_le 10 n (by norm_num) hn
  have hpos : 1 ≤ nd n := by
    unfold nd; rw [Nat.one_le_iff_ne_zero, Ne, List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero]
    exact hn
  rw [show nd n = nd n - 1 + 1 by omega, pow_succ] at h
  omega

theorem nd_pos (n : ℕ) (hn : n ≠ 0) : 1 ≤ nd n := by
  unfold nd; rw [Nat.one_le_iff_ne_zero, Ne, List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero]
  exact hn

theorem nd_ge (n k : ℕ) (h : 10 ^ k ≤ n) : k + 1 ≤ nd n := by
  have h1 := lt_pow_nd n
  by_contra hc
  have : 10 ^ nd n ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem nd_le (n k : ℕ) (h : n < 10 ^ k) (hn : n ≠ 0) : nd n ≤ k := by
  have h1 := pow_nd_le n hn
  by_contra hc
  have : 10 ^ k ≤ 10 ^ (nd n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem nd_one (n : ℕ) (h0 : 0 < n) (h9 : n ≤ 9) : nd n = 1 :=
  le_antisymm (nd_le n 1 (by norm_num; omega) (by omega)) (nd_pos n (by omega))

/-! ### Intervals -/

/-- `x` lies between `lo` and `hi`, the ends included when `closed`. -/
def Inside (closed : Bool) (lo hi x : ℝ) : Prop :=
  if closed then lo ≤ x ∧ x ≤ hi else lo < x ∧ x < hi

variable {closed : Bool} {lo hi : ℝ}

theorem Inside.lo_le {x : ℝ} (h : Inside closed lo hi x) : lo ≤ x := by
  unfold Inside at h; split_ifs at h <;> linarith [h.1]

theorem Inside.le_hi {x : ℝ} (h : Inside closed lo hi x) : x ≤ hi := by
  unfold Inside at h; split_ifs at h <;> linarith [h.2]

theorem Inside.between {a b c : ℝ} (ha : Inside closed lo hi a) (hb : Inside closed lo hi b)
    (h1 : a ≤ c) (h2 : c ≤ b) : Inside closed lo hi c := by
  unfold Inside at ha hb ⊢
  split_ifs at ha hb ⊢ <;> constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- A point below a point of the interval and outside it lies at or below the lower end. -/
theorem le_lo_of_not {b c : ℝ} (hb : Inside closed lo hi b) (hc : ¬ Inside closed lo hi c)
    (h : c ≤ b) : c ≤ lo := by
  by_contra hlt
  push Not at hlt
  apply hc
  unfold Inside at hb ⊢
  split_ifs at hb ⊢ <;> constructor <;> linarith [hb.1, hb.2]

/-- The decimal `m · 10 ^ j`. -/
noncomputable def dv (m : ℕ) (j : ℤ) : ℝ := (m : ℝ) * (10 : ℝ) ^ j

theorem dv_pos (m : ℕ) (hm : 0 < m) (j : ℤ) : 0 < dv m j := by
  unfold dv; have : (0 : ℝ) < m := by exact_mod_cast hm
  positivity

theorem dv_mono {a b : ℕ} (h : a ≤ b) (j : ℤ) : dv a j ≤ dv b j := by
  unfold dv
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  exact mul_le_mul_of_nonneg_right this (zpow_pos (by norm_num) j).le

theorem dv_shift (m n : ℕ) (j : ℤ) : dv (m * 10 ^ n) j = dv m (j + n) := by
  unfold dv
  rw [zpow_add₀ (by norm_num), zpow_natCast]; push_cast; ring

theorem dv_ten (m : ℕ) (j : ℤ) : dv (10 * m) j = dv m (j + 1) := by
  have := dv_shift m 1 j; rw [pow_one, mul_comm] at this; simpa using this

/-- `s · 10 ^ e ≥ c · 10 ^ J` with `e ≤ J` gives `s ≥ c · 10 ^ (J - e)`. -/
theorem nat_ge_of_dv (s c : ℕ) (e J : ℤ) (he : e ≤ J) (h : dv c J ≤ dv s e) :
    c * 10 ^ (J - e).toNat ≤ s := by
  have h1 : dv c J = dv (c * 10 ^ (J - e).toNat) e := by
    rw [dv_shift]; congr 1; omega
  rw [h1] at h
  unfold dv at h
  have hp : (0 : ℝ) < (10 : ℝ) ^ e := zpow_pos (by norm_num) e
  have := le_of_mul_le_mul_right h hp
  exact_mod_cast this

/-- `3 s · 10 ^ e ≥ c · 10 ^ J` with `e ≤ J` gives `3 s ≥ c · 10 ^ (J - e)`. -/
theorem nat_le3_of_dv (s c : ℕ) (e J : ℤ) (he : e ≤ J) (h : dv c J ≤ 3 * dv s e) :
    c * 10 ^ (J - e).toNat ≤ 3 * s := by
  have h1 : dv c J = dv (c * 10 ^ (J - e).toNat) e := by
    rw [dv_shift]; congr 1; omega
  rw [h1] at h
  unfold dv at h
  have hp : (0 : ℝ) < (10 : ℝ) ^ e := zpow_pos (by norm_num) e
  have : ((c * 10 ^ (J - e).toNat : ℕ) : ℝ) ≤ 3 * s := by
    have h2 : ((c * 10 ^ (J - e).toNat : ℕ) : ℝ) * 10 ^ e ≤ (3 * s) * 10 ^ e := by linarith
    exact le_of_mul_le_mul_right h2 hp
  exact_mod_cast this

/-! ### The analysis of significant digits -/

section
variable (closed lo hi)

/-- No multiple of a power of ten above `10 ^ J` lies in the interval. -/
def Top (J : ℤ) : Prop := ∀ j : ℤ, J < j → ∀ m : ℕ, ¬ Inside closed lo hi (dv m j)

end

/-- A multiplier at the top exponent is no multiple of 10. -/
theorem top_mod (J : ℤ) (hJ : Top closed lo hi J) (m : ℕ) (hm : Inside closed lo hi (dv m J)) :
    m % 10 ≠ 0 := by
  intro h
  obtain ⟨q, rfl⟩ : 10 ∣ m := Nat.dvd_of_mod_eq_zero h
  rw [dv_ten] at hm
  exact hJ (J + 1) (by omega) q hm

/-- The multipliers at the top exponent have the same number of digits. -/
theorem same_digits (J : ℤ) (hJ : Top closed lo hi J) (a b : ℕ) (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : Inside closed lo hi (dv a J)) (hb : Inside closed lo hi (dv b J)) : nd a = nd b := by
  wlog hab : a ≤ b generalizing a b
  · exact (this b a hb0 ha0 hb ha (by omega)).symm
  by_contra hne
  have hab' : a < 10 ^ nd b := lt_of_le_of_lt hab (lt_pow_nd b)
  have hle := nd_le a (nd b) hab' (by omega)
  have hlt : nd a < nd b := by omega
  have h1 : a < 10 ^ nd a := lt_pow_nd a
  have h2 : 10 ^ nd a ≤ b := by
    have := pow_nd_le b (by omega)
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) this
  have hin : Inside closed lo hi (dv (10 ^ nd a) J) :=
    ha.between hb (dv_mono h1.le J) (dv_mono h2 J)
  have hpos := nd_pos a (by omega)
  rw [show 10 ^ nd a = 1 * 10 ^ nd a by ring, dv_shift] at hin
  exact hJ (J + nd a) (by omega) 1 hin

/-- A decimal of the interval below the top exponent has more digits than the multipliers at the
top, unless they have one digit and it is a one-digit multiple of `10 ^ (J - 1)`. -/
theorem more_digits (J : ℤ) (hJ : Top closed lo hi J) (_hlo : 0 < lo) (h3 : hi ≤ 3 * lo)
    (m : ℕ) (hm0 : 0 < m) (hm : Inside closed lo hi (dv m J)) (s : ℕ) (e : ℤ) (he : e ≤ J - 1)
    (hs : Inside closed lo hi (dv s e)) :
    nd m + 1 ≤ nd s ∨ (nd m = 1 ∧ e = J - 1 ∧ s ≤ 9) := by
  have hmod := top_mod J hJ m hm
  by_cases hD : nd m = 1
  · -- one digit: the ratio of the ends bounds `s` from below
    have hm9 : m < 10 := by have := lt_pow_nd m; rw [hD] at this; simpa using this
    have hle : dv 1 J ≤ 3 * dv s e := by
      have a1 : dv 1 J ≤ dv m J := dv_mono (by omega) J
      have a2 := hm.le_hi
      have a3 := hs.lo_le
      linarith
    have := nat_le3_of_dv s 1 e J (by omega) hle
    by_cases he1 : e = J - 1
    · have h1 : (J - e).toNat = 1 := by omega
      rw [h1] at this
      by_cases hs9 : s ≤ 9
      · exact Or.inr ⟨hD, he1, hs9⟩
      · left; rw [hD]; exact nd_ge s 1 (by norm_num; omega)
    · left
      rw [hD]
      have h2 : 2 ≤ (J - e).toNat := by omega
      have : 1 * 10 ^ 2 ≤ 1 * 10 ^ (J - e).toNat := by
        rw [one_mul, one_mul]; exact Nat.pow_le_pow_right (by norm_num) h2
      exact nd_ge s 1 (by norm_num; omega)
  · -- several digits: the multiple of 10 below `m` lies outside, below the interval
    have hD2 : 2 ≤ nd m := by have := nd_pos m (by omega); omega
    set c := 10 * (m / 10) with hc
    have hcm : c < m := by omega
    have hcD : 10 ^ (nd m - 1) ≤ c := by
      have h1 := pow_nd_le m (by omega)
      have h2 : 10 ∣ 10 ^ (nd m - 1) := dvd_pow_self 10 (by omega)
      obtain ⟨r, hr⟩ := h2
      omega
    have hcout : ¬ Inside closed lo hi (dv c J) := by
      rw [hc, dv_ten]; exact hJ (J + 1) (by omega) _
    have hcle : dv c J ≤ lo := le_lo_of_not hm hcout (dv_mono hcm.le J)
    have hge := nat_ge_of_dv s c e J (by omega) (le_trans hcle hs.lo_le)
    left
    have h10 : 10 ^ (nd m - 1) * 10 ^ 1 ≤ c * 10 ^ (J - e).toNat :=
      Nat.mul_le_mul hcD (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [← pow_add, show nd m - 1 + 1 = nd m by omega] at h10
    exact nd_ge s (nd m) (le_trans h10 hge)

/-! ### The choice -/

/-- `x` is no farther from `v` than `y`, and at an equal distance `x = y` or `t` is even. -/
def Near (x y v : ℝ) (t : ℕ) : Prop :=
  |x - v| < |y - v| ∨ (|x - v| = |y - v| ∧ (x = y ∨ t % 2 = 0))

/-- The choice of the printers: the nearest multiple at the top exponent `J`, nearer than every
one-digit multiple at `J - 1`, or a one-digit multiple at `J - 1` nearer than every multiple at
`J` and nearest among the one-digit multiples at `J - 1`. -/
def Choice (closed : Bool) (lo hi v : ℝ) (J : ℤ) (t : ℕ) (k : ℤ) : Prop :=
  (k = J ∧ (∀ m : ℕ, Inside closed lo hi (dv m J) → Near (dv t J) (dv m J) v t) ∧
      ∀ m : ℕ, m ≤ 9 → Inside closed lo hi (dv m (J - 1)) → |dv t J - v| < |dv m (J - 1) - v|) ∨
    (k = J - 1 ∧ t ≤ 9 ∧ (∀ m : ℕ, Inside closed lo hi (dv m J) → |dv t (J - 1) - v| < |dv m J - v|) ∧
      ∀ m : ℕ, m ≤ 9 → Inside closed lo hi (dv m (J - 1)) → Near (dv t (J - 1)) (dv m (J - 1)) v t)

/-- The chosen decimal has the fewest significant digits among the decimals of the interval, the
least distance from `v` among those with as many digits, and an even last digit at an equal
distance from a different one. -/
theorem shortest_of_choice (closed : Bool) (lo hi v : ℝ) (hlo : 0 < lo) (h3 : hi ≤ 3 * lo)
    (J : ℤ) (hJ : Top closed lo hi J) (hex : ∃ m, Inside closed lo hi (dv m J))
    (t : ℕ) (k : ℤ) (ht0 : 0 < t) (ht : Inside closed lo hi (dv t k)) (hc : Choice closed lo hi v J t k) :
    t % 10 ≠ 0 ∧ ∀ d e, 0 < d → Inside closed lo hi (dv d e) →
      sigDigits t < sigDigits d ∨
      (sigDigits t = sigDigits d ∧
        (|dv t k - v| < |dv d e - v| ∨
         (|dv t k - v| = |dv d e - v| ∧ (dv t k = dv d e ∨ stripZeros t % 2 = 0)))) := by
  obtain ⟨m0, hm0⟩ := hex
  have hm00 : 0 < m0 := by
    by_contra h
    have : m0 = 0 := by omega
    subst this
    have := hm0.lo_le; unfold dv at this; simp at this; linarith
  have htmod : t % 10 ≠ 0 := by
    rcases hc with ⟨hk, _⟩ | ⟨hk, ht9, _⟩
    · rw [hk] at ht; exact top_mod J hJ t ht
    · omega
  refine ⟨htmod, ?_⟩
  rw [stripZeros_self t htmod]
  have hsigt : sigDigits t = nd t := by unfold sigDigits nd; rw [stripZeros_self t htmod]
  -- the number of digits of the chosen decimal is that of the multipliers at `J`
  have hndt : nd t = nd m0 := by
    rcases hc with ⟨hk, _⟩ | ⟨hk, ht9, _⟩
    · rw [hk] at ht; exact same_digits J hJ t m0 ht0 hm00 ht hm0
    · rw [hk] at ht
      rcases more_digits J hJ hlo h3 m0 hm00 hm0 t (J - 1) le_rfl ht with h | ⟨h, _⟩
      · rw [nd_one t ht0 ht9] at h; have := nd_pos m0 (by omega); omega
      · rw [nd_one t ht0 ht9, h]
  intro d e hd hde
  obtain ⟨hs0, hsmod, z, hz⟩ := stripZeros_spec d hd
  set s := stripZeros d with hsdef
  have hsig : sigDigits d = nd s := rfl
  have hval : dv d e = dv s (e + z) := by rw [hz, dv_shift]
  rw [hval] at hde ⊢
  rw [hsigt, hsig]
  set e' := e + (z : ℤ) with he'
  -- the exponent of `s` is at most `J`
  have heJ : e' ≤ J := by
    by_contra h; push Not at h; exact hJ e' h s hde
  rcases lt_trichotomy e' (J - 1) with hlt | heq | hgt
  · rcases more_digits J hJ hlo h3 m0 hm00 hm0 s e' (by omega) hde with h | ⟨_, h, _⟩
    · left; omega
    · omega
  · rcases more_digits J hJ hlo h3 m0 hm00 hm0 s e' (by omega) hde with h | ⟨h1, _, h9⟩
    · left; omega
    · right
      refine ⟨by rw [hndt, h1, nd_one s hs0 h9], ?_⟩
      rw [heq] at hde ⊢
      rcases hc with ⟨hk, _, hfar⟩ | ⟨hk, _, _, hnear⟩
      · rw [hk]; exact Or.inl (hfar s h9 hde)
      · rw [hk]; exact hnear s h9 hde
  · have hJe : e' = J := by omega
    rw [hJe] at hde ⊢
    right
    refine ⟨by rw [hndt]; exact same_digits J hJ m0 s hm00 hs0 hm0 hde, ?_⟩
    rcases hc with ⟨hk, hnear, _⟩ | ⟨hk, _, hfar, _⟩
    · rw [hk]; exact hnear s hde
    · rw [hk]; exact Or.inl (hfar s hde)

#print axioms same_digits
#print axioms more_digits
#print axioms shortest_of_choice

end Verified.Examples.PrintFloatShort
