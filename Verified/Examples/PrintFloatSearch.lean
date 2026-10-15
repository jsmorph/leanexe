import Verified.Examples.PrintFloatQuot
import Verified.Examples.ParseFloatDigits

/-!
The search of `PrintFloat.shortest` for the top exponent.  For a word of significand `Q ≥ 1` and
binade `E ≥ 1` of a format with least subnormal `2 ^ -nu`, `lo`, `hi`, and `vv` are the ends of
the rounding interval and the value, as reals, and `Ex j` says that a multiple of `10 ^ j` lies in
the interval.  `Ex` holds from `-nu` down (`ex_low`, `ex_down`) and fails from the exponent `js`
of `startExp` up (`not_ex_start`), so `top` is the largest `j` with `Ex j`; above it no multiple
of a power of ten lies in the interval (`top_top`), and from `top - 1` on the quotients that the
code takes stay below `2 ^ 61` (`quot_bound`).  `found` decides `Ex` there (`found_iff`), and the
search returns `js - top` (`search_spec`).
-/

namespace Verified.Examples.PrintFloatSearch
open PrintFloat Uscale UscaleTheorem ParseFloatRound PrintFloatShort PrintFloatQuot
open scoped Classical

set_option exponentiation.threshold 4096

/-- The quarter-unit numerator of the lower end. -/
def nl (Q : ℕ) (low : Bool) : ℕ := if low then 4 * Q - 1 else 4 * Q - 2

/-- The lower end of the rounding interval. -/
noncomputable def lo (Q E nu : ℕ) (low : Bool) : ℝ := rv (nl Q low) (E - 1) (nu + 2)

/-- The upper end of the rounding interval. -/
noncomputable def hi (Q E nu : ℕ) : ℝ := rv (4 * Q + 2) (E - 1) (nu + 2)

/-- The value of the word. -/
noncomputable def vv (Q E nu : ℕ) : ℝ := rv (4 * Q) (E - 1) (nu + 2)

/-- The ends belong to the interval when `Q` is even. -/
def cl (Q : ℕ) : Bool := decide (Q % 2 = 0)

/-- A multiple of `10 ^ j` lies in the interval. -/
def Ex (Q E nu : ℕ) (low : Bool) (j : ℤ) : Prop :=
  ∃ m : ℕ, Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv m j)

variable {Q E nu : ℕ} {low : Bool}

theorem rv_pos (N sn sd : ℕ) (hN : 0 < N) : 0 < rv N sn sd := by
  unfold rv; have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

theorem rv_sub (a b sn sd : ℕ) (h : b ≤ a) : rv a sn sd - rv b sn sd = rv (a - b) sn sd := by
  unfold rv; rw [Nat.cast_sub h]; ring

theorem rv_le (a b sn sd : ℕ) (h : a ≤ b) : rv a sn sd ≤ rv b sn sd := by
  unfold rv
  have : (a : ℝ) ≤ b := by exact_mod_cast h
  have h2 : (0 : ℝ) < 2 ^ sn / 2 ^ sd := by positivity
  rw [mul_div_assoc, mul_div_assoc]; exact mul_le_mul_of_nonneg_right this h2.le

theorem nl_pos (hQ : 1 ≤ Q) : 0 < nl Q low := by unfold nl; split_ifs <;> omega

theorem lo_pos (hQ : 1 ≤ Q) : 0 < lo Q E nu low := rv_pos _ _ _ (nl_pos hQ)

theorem hi_le (hQ : 1 ≤ Q) : hi Q E nu ≤ 3 * lo Q E nu low := by
  unfold hi lo rv
  have h : ((4 * Q + 2 : ℕ) : ℝ) ≤ 3 * (nl Q low : ℝ) := by
    have : 4 * Q + 2 ≤ 3 * nl Q low := by unfold nl; split_ifs <;> omega
    exact_mod_cast this
  have h2 : (0 : ℝ) < 2 ^ (E - 1) / 2 ^ (nu + 2) := by positivity
  rw [mul_div_assoc, mul_div_assoc]
  nlinarith

theorem lo_lt_vv (hQ : 1 ≤ Q) : lo Q E nu low < vv Q E nu := by
  unfold lo vv rv
  have h : (nl Q low : ℝ) < ((4 * Q : ℕ) : ℝ) := by
    have : nl Q low < 4 * Q := by unfold nl; split_ifs <;> omega
    exact_mod_cast this
  have h2 : (0 : ℝ) < 2 ^ (E - 1) / 2 ^ (nu + 2) := by positivity
  rw [mul_div_assoc, mul_div_assoc]
  nlinarith

theorem vv_lt_hi : vv Q E nu < hi Q E nu := by
  unfold vv hi rv
  have h : ((4 * Q : ℕ) : ℝ) < ((4 * Q + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 4 * Q < 4 * Q + 2)
  have h2 : (0 : ℝ) < 2 ^ (E - 1) / 2 ^ (nu + 2) := by positivity
  rw [mul_div_assoc, mul_div_assoc]
  nlinarith

/-- The width of the interval, in quarter units: 4, or 3 at the start of a normal binade. -/
theorem width_eq (hQ : 1 ≤ Q) :
    hi Q E nu - lo Q E nu low = rv (if low then 3 else 4) (E - 1) (nu + 2) := by
  unfold hi lo
  rw [rv_sub _ _ _ _ (by unfold nl; split_ifs <;> omega)]
  congr 1
  unfold nl; split_ifs <;> omega

theorem width_pos (hQ : 1 ≤ Q) : 0 < hi Q E nu - lo Q E nu low := by
  rw [width_eq hQ]; apply rv_pos; split_ifs <;> norm_num

/-! ### Where multiples lie -/

theorem ex_down (j : ℤ) (h : Ex Q E nu low j) : Ex Q E nu low (j - 1) := by
  obtain ⟨m, hm⟩ := h
  refine ⟨10 * m, ?_⟩
  rw [dv_ten, sub_add_cancel]; exact hm

theorem ex_down' (j i : ℤ) (hij : i ≤ j) (h : Ex Q E nu low j) : Ex Q E nu low i := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, j = i + n := ⟨(j - i).toNat, by omega⟩
  subst hn
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have := ex_down (i + (n + 1 : ℕ)) h
    apply ih (by omega)
    rwa [show (i + ((n + 1 : ℕ) : ℤ) - 1) = i + (n : ℤ) by push_cast; ring] at this

/-- An interval wider than `10 ^ j` holds a multiple of `10 ^ j`. -/
theorem ex_of_small (hQ : 1 ≤ Q) (j : ℤ) (h : (10 : ℝ) ^ j < hi Q E nu - lo Q E nu low) :
    Ex Q E nu low j := by
  have hp : (0 : ℝ) < 10 ^ j := zpow_pos (by norm_num) j
  have hl := lo_pos (Q := Q) (E := E) (nu := nu) (low := low) hQ
  set m := Nat.floor (lo Q E nu low / 10 ^ j) + 1 with hm
  have h1 : lo Q E nu low / 10 ^ j < m := by rw [hm]; push_cast; exact Nat.lt_floor_add_one _
  have h2 : (m : ℝ) ≤ lo Q E nu low / 10 ^ j + 1 := by
    rw [hm]; push_cast; linarith [Nat.floor_le (div_nonneg hl.le hp.le)]
  refine ⟨m, ?_⟩
  have a1 : lo Q E nu low < dv m j := by
    unfold dv; rw [div_lt_iff₀ hp] at h1; linarith
  have a2 : dv m j < hi Q E nu := by
    unfold dv
    have : (m : ℝ) * 10 ^ j ≤ lo Q E nu low + 10 ^ j := by
      have := mul_le_mul_of_nonneg_right h2 hp.le
      rwa [add_mul, div_mul_cancel₀ _ hp.ne', one_mul] at this
    linarith
  unfold Inside; split_ifs <;> constructor <;> linarith

/-- No multiple of `10 ^ j` lies in the interval when `10 ^ j` exceeds its upper end. -/
theorem not_ex_of_big (hQ : 1 ≤ Q) (j : ℤ) (h : hi Q E nu < (10 : ℝ) ^ j) : ¬ Ex Q E nu low j := by
  rintro ⟨m, hm⟩
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    have := hm.lo_le; unfold dv at this; simp at this
    linarith [lo_pos (Q := Q) (E := E) (nu := nu) (low := low) hQ]
  · have := hm.le_hi
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h0
    have : (10 : ℝ) ^ j ≤ dv m j := by
      unfold dv; have := zpow_pos (show (0 : ℝ) < 10 by norm_num) j; nlinarith
    linarith

/-- Multiples of `10 ^ -nu` lie in the interval. -/
theorem ex_low (hQ : 1 ≤ Q) (_hE : 1 ≤ E) (hnu : 1 ≤ nu) : Ex Q E nu low (-(nu : ℤ)) := by
  apply ex_of_small hQ
  rw [width_eq hQ]
  unfold rv
  have h3 : (3 : ℝ) ≤ ((if low then 3 else 4 : ℕ) : ℝ) := by split_ifs <;> norm_num
  have hE' : (1 : ℝ) ≤ 2 ^ (E - 1) := one_le_pow₀ (by norm_num)
  have h4 : (10 : ℝ) ^ (-(nu : ℤ)) = 1 / 10 ^ nu := by rw [zpow_neg, zpow_natCast, one_div]
  rw [h4, pow_add]
  have hp : (0 : ℝ) < 2 ^ nu := by positivity
  have hq : (4 : ℝ) * 2 ^ nu < 3 * 10 ^ nu := by
    have : (2 : ℝ) ^ nu ≤ 10 ^ nu := pow_le_pow_left₀ (by norm_num) (by norm_num) nu
    have h2 : (2 : ℝ) ^ nu * 2 ≤ 10 ^ nu := by
      calc (2 : ℝ) ^ nu * 2 ≤ 2 ^ nu * 5 ^ nu := by
            have : (2 : ℝ) ≤ 5 ^ nu := by
              calc (2 : ℝ) ≤ 5 ^ 1 := by norm_num
                _ ≤ 5 ^ nu := pow_le_pow_right₀ (by norm_num) hnu
            nlinarith
        _ = 10 ^ nu := by rw [← mul_pow]; norm_num
    nlinarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h10 : (0 : ℝ) < 10 ^ nu := by positivity
  have h5 : (3 : ℝ) * 10 ^ nu ≤ ((if low then 3 else 4 : ℕ) : ℝ) * 2 ^ (E - 1) * 10 ^ nu := by
    have : (3 : ℝ) * 1 ≤ ((if low then 3 else 4 : ℕ) : ℝ) * 2 ^ (E - 1) :=
      mul_le_mul h3 hE' (by norm_num) (by positivity)
    have := mul_le_mul_of_nonneg_right this h10.le
    linarith
  linarith

/-! ### The start of the search -/

theorem two_pow_le_ten (b : ℕ) : (2 : ℕ) ^ b ≤ 10 ^ ((31 * b + 99) / 100) := by
  have h1 : (2 ^ b) ^ 100 ≤ (10 ^ ((31 * b + 99) / 100)) ^ 100 := by
    calc (2 ^ b) ^ 100 = (2 ^ 100) ^ b := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (10 ^ 31) ^ b := Nat.pow_le_pow_left (by norm_num) b
      _ = 10 ^ (31 * b) := by rw [← pow_mul]
      _ ≤ 10 ^ (100 * ((31 * b + 99) / 100)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (10 ^ ((31 * b + 99) / 100)) ^ 100 := by rw [← pow_mul, mul_comm]
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1

theorem ten_pow_le_two (a : ℕ) : (10 : ℕ) ^ (3 * a / 10) ≤ 2 ^ a := by
  have h1 : (10 ^ (3 * a / 10)) ^ 10 ≤ (2 ^ a) ^ 10 := by
    calc (10 ^ (3 * a / 10)) ^ 10 = 10 ^ (10 * (3 * a / 10)) := by rw [← pow_mul, mul_comm]
      _ ≤ 10 ^ (3 * a) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (10 ^ 3) ^ a := by rw [← pow_mul]
      _ ≤ (2 ^ 10) ^ a := Nat.pow_le_pow_left (by norm_num) a
      _ = (2 ^ a) ^ 10 := by rw [← pow_mul, ← pow_mul, mul_comm]
  exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1

/-- The unbiased start of the search. -/
def jstart (Q E nu : ℕ) : ℤ :=
  if nu + 2 ≤ Nat.size (4 * Q + 2) + (E - 1) then
    ((31 * (Nat.size (4 * Q + 2) + (E - 1) - (nu + 2)) + 99) / 100 : ℕ)
  else -((3 * (nu + 2 - (Nat.size (4 * Q + 2) + (E - 1))) / 10 : ℕ) : ℤ)

theorem hi_lt_start : hi Q E nu < (10 : ℝ) ^ jstart Q E nu := by
  have hs : 4 * Q + 2 < 2 ^ Nat.size (4 * Q + 2) := Nat.lt_size_self _
  set b := Nat.size (4 * Q + 2) + (E - 1) with hb
  have hhi : hi Q E nu < (2 : ℝ) ^ b / 2 ^ (nu + 2) := by
    unfold hi rv
    have this' : ((4 * Q + 2 : ℕ) : ℝ) < 2 ^ Nat.size (4 * Q + 2) := by exact_mod_cast hs
    rw [show (2 : ℝ) ^ b = 2 ^ Nat.size (4 * Q + 2) * 2 ^ (E - 1) by rw [hb, pow_add],
      div_lt_div_iff_of_pos_right (by positivity)]
    have : (0 : ℝ) < 2 ^ (E - 1) := by positivity
    exact mul_lt_mul_of_pos_right this' this
  unfold jstart
  rw [← hb]
  split_ifs with h
  · have h2 := two_pow_le_ten (b - (nu + 2))
    rw [zpow_natCast]
    have e : (2 : ℝ) ^ b / 2 ^ (nu + 2) = 2 ^ (b - (nu + 2)) := by
      rw [div_eq_iff (by positivity), ← pow_add, Nat.sub_add_cancel h]
    rw [e] at hhi
    have : (2 : ℝ) ^ (b - (nu + 2)) ≤ 10 ^ ((31 * (b - (nu + 2)) + 99) / 100) := by exact_mod_cast h2
    linarith
  · have h2 := ten_pow_le_two (nu + 2 - b)
    rw [zpow_neg, zpow_natCast]
    have e : (2 : ℝ) ^ b / 2 ^ (nu + 2) = 1 / 2 ^ (nu + 2 - b) := by
      rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
      congr 1; omega
    rw [e] at hhi
    have h3 : (10 : ℝ) ^ (3 * (nu + 2 - b) / 10) ≤ 2 ^ (nu + 2 - b) := by exact_mod_cast h2
    have h4 : (1 : ℝ) / 2 ^ (nu + 2 - b) ≤ (10 ^ (3 * (nu + 2 - b) / 10))⁻¹ := by
      rw [one_div]; exact inv_anti₀ (by positivity) h3
    linarith

theorem not_ex_start (hQ : 1 ≤ Q) (j : ℤ) (hj : jstart Q E nu ≤ j) : ¬ Ex Q E nu low j := by
  apply not_ex_of_big hQ
  exact lt_of_lt_of_le hi_lt_start (zpow_le_zpow_right₀ (by norm_num) hj)

/-! ### The top exponent -/

theorem ex_some (hQ : 1 ≤ Q) (hE : 1 ≤ E) (hnu : 1 ≤ nu) :
    ∃ i : ℕ, Ex Q E nu low (jstart Q E nu - i) := by
  refine ⟨(jstart Q E nu + nu).toNat, ?_⟩
  apply ex_down' _ _ ?_ (ex_low hQ hE hnu)
  by_cases h : 0 ≤ jstart Q E nu + nu
  · omega
  · exfalso
    have := not_ex_start (Q := Q) (E := E) (nu := nu) (low := low) hQ (-(nu : ℤ)) (by omega)
    exact this (ex_low hQ hE hnu)

/-- The number of steps of the search. -/
noncomputable def steps (Q E nu : ℕ) (low : Bool) (hQ : 1 ≤ Q) (hE : 1 ≤ E) (hnu : 1 ≤ nu) : ℕ :=
  Nat.find (ex_some (low := low) hQ hE hnu)

/-- The top exponent. -/
noncomputable def top (Q E nu : ℕ) (low : Bool) (hQ : 1 ≤ Q) (hE : 1 ≤ E) (hnu : 1 ≤ nu) : ℤ :=
  jstart Q E nu - steps Q E nu low hQ hE hnu

section
variable (hQ : 1 ≤ Q) (hE : 1 ≤ E) (hnu : 1 ≤ nu)
include hQ hE hnu

theorem ex_top : Ex Q E nu low (top Q E nu low hQ hE hnu) :=
  Nat.find_spec (ex_some (low := low) hQ hE hnu)

theorem steps_pos : 1 ≤ steps Q E nu low hQ hE hnu := by
  by_contra h
  have h0 : steps Q E nu low hQ hE hnu = 0 := by omega
  have := ex_top (low := low) hQ hE hnu
  unfold top at this; rw [h0] at this; simp at this
  exact not_ex_start hQ _ le_rfl this

theorem top_top : Top (cl Q) (lo Q E nu low) (hi Q E nu) (top Q E nu low hQ hE hnu) := by
  intro j hj m hm
  by_cases hjs : j < jstart Q E nu
  · have hi' : (jstart Q E nu - j).toNat < steps Q E nu low hQ hE hnu := by
      unfold top at hj; omega
    have := Nat.find_min (ex_some (low := low) hQ hE hnu) hi'
    apply this
    rw [show jstart Q E nu - ((jstart Q E nu - j).toNat : ℕ) = j by omega]
    exact ⟨m, hm⟩
  · exact not_ex_start hQ j (by omega) ⟨m, hm⟩

theorem top_ge : -(nu : ℤ) ≤ top Q E nu low hQ hE hnu := by
  by_contra h
  push Not at h
  exact top_top (low := low) hQ hE hnu (-(nu : ℤ)) h _ (ex_low hQ hE hnu).choose_spec

theorem top_lt_start : top Q E nu low hQ hE hnu < jstart Q E nu := by
  have := steps_pos (low := low) hQ hE hnu; unfold top; omega

/-- Above the top exponent the interval is narrower than `10 ^ (top + 1)`. -/
theorem width_le : hi Q E nu - lo Q E nu low ≤ (10 : ℝ) ^ (top Q E nu low hQ hE hnu + 1) := by
  by_contra h
  push Not at h
  obtain ⟨m, hm⟩ := ex_of_small hQ _ h
  exact top_top (low := low) hQ hE hnu _ (by omega) m hm

end

/-! ### The size of the quotients -/

/-- From `top - 1` on, the quotients of the upper end by `10 ^ j` stay below `2 ^ 61`. -/
theorem quot_bound (hQ : 1 ≤ Q) (hE : 1 ≤ E) (hnu : 1 ≤ nu) (hQ53 : Q < 2 ^ 53) (N : ℕ)
    (hN : N ≤ 8 * Q + 4) (j : ℤ) (hj : top Q E nu low hQ hE hnu - 1 ≤ j) :
    num N (E - 1) j < den (nu + 2) j * 2 ^ 62 := by
  have hd := den_pos (nu + 2) j
  have hw := width_le (low := low) hQ hE hnu
  rw [width_eq hQ] at hw
  -- the real `N · 2 ^ (E-1) / 2 ^ (nu+2) / 10 ^ j`
  have hq : (num N (E - 1) j : ℝ) / den (nu + 2) j = rv N (E - 1) (nu + 2) / 10 ^ j :=
    (rv_div N (E - 1) (nu + 2) j).symm
  have hU : (0 : ℝ) < 2 ^ (E - 1) / 2 ^ (nu + 2) := by positivity
  have hp : (0 : ℝ) < (10 : ℝ) ^ j := zpow_pos (by norm_num) j
  have h10 : (10 : ℝ) ^ (top Q E nu low hQ hE hnu + 1) ≤ 100 * 10 ^ j := by
    have : top Q E nu low hQ hE hnu + 1 ≤ j + 2 := by omega
    calc (10 : ℝ) ^ (top Q E nu low hQ hE hnu + 1) ≤ 10 ^ (j + 2) :=
          zpow_le_zpow_right₀ (by norm_num) this
      _ = 100 * 10 ^ j := by rw [zpow_add₀ (by norm_num)]; norm_num; ring
  have hwid : (3 : ℝ) * (2 ^ (E - 1) / 2 ^ (nu + 2)) ≤ 100 * 10 ^ j := by
    have : (3 : ℝ) * (2 ^ (E - 1) / 2 ^ (nu + 2)) ≤ rv (if low then 3 else 4) (E - 1) (nu + 2) := by
      unfold rv
      have : (3 : ℝ) ≤ ((if low then 3 else 4 : ℕ) : ℝ) := by split_ifs <;> norm_num
      rw [mul_div_assoc]; nlinarith
    linarith
  have hrv : rv N (E - 1) (nu + 2) ≤ (8 * Q + 4) * (2 ^ (E - 1) / 2 ^ (nu + 2)) := by
    unfold rv
    have : (N : ℝ) ≤ 8 * Q + 4 := by exact_mod_cast hN
    rw [mul_div_assoc]; nlinarith
  have hfin : rv N (E - 1) (nu + 2) / 10 ^ j < 2 ^ 62 := by
    rw [div_lt_iff₀ hp]
    have hU' : 2 ^ (E - 1) / 2 ^ (nu + 2) ≤ (100 / 3 : ℝ) * 10 ^ j := by linarith
    have hQ' : (8 * Q + 4 : ℝ) * (100 / 3) < 2 ^ 62 := by
      have : (Q : ℝ) < 2 ^ 53 := by exact_mod_cast hQ53
      linarith
    calc rv N (E - 1) (nu + 2) ≤ (8 * Q + 4) * (2 ^ (E - 1) / 2 ^ (nu + 2)) := hrv
      _ ≤ (8 * Q + 4) * ((100 / 3 : ℝ) * 10 ^ j) :=
          mul_le_mul_of_nonneg_left hU' (by positivity)
      _ = (8 * Q + 4) * (100 / 3 : ℝ) * 10 ^ j := by ring
      _ < 2 ^ 62 * 10 ^ j := mul_lt_mul_of_pos_right hQ' hp
  rw [← hq, div_lt_iff₀ (by exact_mod_cast hd)] at hfin
  rw [mul_comm]
  exact_mod_cast hfin

#print axioms top_top
#print axioms width_le
#print axioms quot_bound

end Verified.Examples.PrintFloatSearch
