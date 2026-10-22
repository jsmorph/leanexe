import Library.Numerics.Decimal.PrintFloat.PrintFloatPick

/-!
The choice of `PrintFloat.shortest` at the top exponent `J`.  `range_inside` reads the multipliers
in the interval off `range`, and `quot_half` reads `⌊2 v / 10 ^ j⌋` and its remainder flag off
`quotAt`.  The nearest multiplier at `J`, clamped into the run, satisfies `Near` against every
multiplier at `J` (`near_scaled`).  When it has one digit, the code compares it with the nearest
one-digit multiplier at `J - 1` through `⌊2 v / 10 ^ (J - 1)⌋`; `no_tie` shows that the two are
never at the same distance from the value, by the factor `5 ^ (1 - J)` that the equation of a tie
would need in a number below 100.  `shortest_spec` concludes that the code's decimal lies in the
interval and is `PrintFloatShort.Choice`.
-/

namespace Library.Numerics.Decimal.PrintFloat.PrintFloatChoice
open PrintFloat Library.Numerics.Arithmetic.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.ParseFloat.ParseFloatRound PrintFloatShort PrintFloatQuot PrintFloatSearch
  PrintFloatPick

set_option exponentiation.threshold 4096

variable {Q E nu : ℕ} {low : Bool}

/-! ### Floors as reals -/

theorem floor_le (a d : ℕ) (_hd : 0 < d) : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := Nat.cast_div_le

theorem lt_floor (a d : ℕ) (hd : 0 < d) : (a : ℝ) / d < ((a / d : ℕ) : ℝ) + 1 := by
  have h : a < (a / d + 1) * d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_iff₀ hd']
  exact_mod_cast h

theorem floor_ne (a d : ℕ) (hd : 0 < d) : a % d ≠ 0 ↔ ((a / d : ℕ) : ℝ) ≠ (a : ℝ) / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · intro h he
    apply h
    rw [eq_div_iff hd'.ne'] at he
    have : a / d * d = a := by exact_mod_cast he
    have h2 := Nat.div_add_mod a d
    rw [Nat.mul_comm] at this
    omega
  · intro h hm
    apply h
    have : a / d * d = a := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
    rw [eq_div_iff hd'.ne']
    exact_mod_cast this

/-! ### The words of the scales -/

theorem sn1 (hb : WordBounds Q E nu) : (UInt64.ofNat E - 1 + 1).toNat = E := by
  obtain ⟨_, _, _, w4, _, _⟩ := words_spec (low := false) hb
  rw [toNat_add' _ _ (by rw [w4]; simp; have := hb.hE2; omega), w4]
  have := hb.hE; simp; omega

/-- The multipliers at `j` in the interval are the run of `range`. -/
theorem range_inside (hb : WordBounds Q E nu) (jb : UInt64)
    (hj1 : 2 ^ 62 - 2 ^ 19 ≤ jb.toNat) (hj2 : jb.toNat ≤ 2 ^ 62 + 2 ^ 19)
    (hj : top Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega) - 1 ≤ (jb.toNat : ℤ) - 2 ^ 62) :
    (∀ m : ℕ, Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv m ((jb.toNat : ℤ) - 2 ^ 62)) ↔
      (range (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2) (4 * UInt64.ofNat Q + 2)
          (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) jb ((UInt64.ofNat Q &&& 1) == 0)).1.toNat ≤ m ∧
        m < (range (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2)
          (4 * UInt64.ofNat Q + 2) (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) jb
          ((UInt64.ofNat Q &&& 1) == 0)).2.toNat) ∧
      (range (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2) (4 * UInt64.ofNat Q + 2)
          (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) jb ((UInt64.ofNat Q &&& 1) == 0)).2.toNat ≤
        2 ^ 62 := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := words_spec (low := low) hb
  set j : ℤ := (jb.toNat : ℤ) - 2 ^ 62 with hjdef
  have hsn : (UInt64.ofNat E - 1).toNat < 2 ^ 30 := by rw [w4]; have := hb.hE2; omega
  have hsd : (UInt64.ofNat nu + 2).toNat < 2 ^ 30 := by rw [w5]; have := hb.hnu2; omega
  have bl := quot_bound hb.hQ hb.hE _ hb.hQ53 (nl Q low) (by unfold nl; split_ifs <;> omega) j hj
  have bh := quot_bound hb.hQ hb.hE _ hb.hQ53 (4 * Q + 2) (by omega) j hj
  obtain ⟨r1, r2⟩ := range_spec ((UInt64.ofNat Q &&& 1) == 0)
    (if low then 4 * UInt64.ofNat Q - 1 else 4 * UInt64.ofNat Q - 2) (4 * UInt64.ofNat Q + 2)
    (UInt64.ofNat E - 1) (UInt64.ofNat nu + 2) jb hsn hsd hj1 hj2
    (by rw [w3, w4, w5, ← hjdef]; exact bl) (by rw [w2, w4, w5, ← hjdef]; exact bh)
  rw [w3, w4, w5, ← hjdef] at r1
  rw [w2, w4, w5, ← hjdef] at r2
  conv at r1 => rhs; rw [w6]
  conv at r2 => rhs; rw [w6]
  refine ⟨fun m => ?_, ?_⟩
  · rw [r1, r2]
    unfold lo hi
    exact inside_iff (cl Q) (nl Q low) (4 * Q + 2) (E - 1) (nu + 2) m j
  · rw [r2]
    have hd := den_pos (nu + 2) j
    unfold floorOf1
    have : num (4 * Q + 2) (E - 1) j / den (nu + 2) j < 2 ^ 62 := by
      rw [Nat.div_lt_iff_lt_mul hd]; linarith
    split_ifs <;> omega

/-- `quotAt` of the value with one more power of two is `⌊2 v / 10 ^ j⌋` with its flag. -/
theorem quot_half (hb : WordBounds Q E nu) (jb : UInt64)
    (hj1 : 2 ^ 62 - 2 ^ 19 ≤ jb.toNat) (hj2 : jb.toNat ≤ 2 ^ 62 + 2 ^ 19)
    (hj : top Q E nu low hb.hQ hb.hE (by have := hb.hnu; omega) - 1 ≤ (jb.toNat : ℤ) - 2 ^ 62) :
    ((quotAt (4 * UInt64.ofNat Q) (UInt64.ofNat E - 1 + 1) (UInt64.ofNat nu + 2) jb).1.toNat : ℝ) ≤
        2 * (vv Q E nu / 10 ^ ((jb.toNat : ℤ) - 2 ^ 62)) ∧
      2 * (vv Q E nu / 10 ^ ((jb.toNat : ℤ) - 2 ^ 62)) <
        ((quotAt (4 * UInt64.ofNat Q) (UInt64.ofNat E - 1 + 1) (UInt64.ofNat nu + 2) jb).1.toNat : ℝ) + 1 ∧
      (quotAt (4 * UInt64.ofNat Q) (UInt64.ofNat E - 1 + 1) (UInt64.ofNat nu + 2) jb).2 =
        decide (((quotAt (4 * UInt64.ofNat Q) (UInt64.ofNat E - 1 + 1) (UInt64.ofNat nu + 2) jb).1.toNat
          : ℝ) ≠ 2 * (vv Q E nu / 10 ^ ((jb.toNat : ℤ) - 2 ^ 62))) ∧
      (quotAt (4 * UInt64.ofNat Q) (UInt64.ofNat E - 1 + 1) (UInt64.ofNat nu + 2) jb).1.toNat < 2 ^ 62 := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := words_spec (low := low) hb
  have w7 := sn1 hb
  set j : ℤ := (jb.toNat : ℤ) - 2 ^ 62 with hjdef
  have hd := den_pos (nu + 2) j
  have hE1 := hb.hE
  have he : num (4 * Q) E j = num (8 * Q) (E - 1) j := by
    unfold num
    rw [show E = E - 1 + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have bv := quot_bound hb.hQ hb.hE _ hb.hQ53 (8 * Q) (by omega) j hj
  rw [← he] at bv
  obtain ⟨q1, q2⟩ := quotAt_spec (4 * UInt64.ofNat Q) (UInt64.ofNat E - 1 + 1) (UInt64.ofNat nu + 2) jb
    (by rw [w7]; have := hb.hE2; omega) (by rw [w5]; have := hb.hnu2; omega) hj1 hj2
    (by rw [w1, w7, w5, ← hjdef]; exact lt_of_lt_of_le bv (Nat.mul_le_mul_left _ (by norm_num)))
  rw [w1, w7, w5, ← hjdef] at q1 q2
  have h2v : 2 * (vv Q E nu / 10 ^ j) = (num (4 * Q) E j : ℝ) / den (nu + 2) j := by
    rw [← rv_div]
    unfold vv rv
    rw [show E = E - 1 + 1 by omega, pow_succ]
    simp only [Nat.add_sub_cancel]
    ring
  have hdr : (0 : ℝ) < den (nu + 2) j := by exact_mod_cast hd
  rw [q1, q2, h2v]
  refine ⟨floor_le _ _ hd, lt_floor _ _ hd, ?_, ?_⟩
  · rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
    exact floor_ne _ _ hd
  · rw [Nat.div_lt_iff_lt_mul hd]; linarith

/-! ### Distances -/

theorem dv_sub (m : ℕ) (j : ℤ) (v : ℝ) : dv m j - v = ((m : ℝ) - v / 10 ^ j) * 10 ^ j := by
  unfold dv
  have : (10 : ℝ) ^ j ≠ 0 := (zpow_pos (by norm_num) j).ne'
  field_simp

theorem abs_dv (m : ℕ) (j : ℤ) (v : ℝ) : |dv m j - v| = |(m : ℝ) - v / 10 ^ j| * 10 ^ j := by
  rw [dv_sub, abs_mul, abs_of_pos (zpow_pos (show (0 : ℝ) < 10 by norm_num) j)]

/-- `Near` at one exponent follows from the comparison of the multipliers with `v / 10 ^ j`. -/
theorem near_scaled (j : ℤ) (v : ℝ) (c m : ℕ)
    (h : |(c : ℝ) - v / 10 ^ j| < |(m : ℝ) - v / 10 ^ j| ∨
      (|(c : ℝ) - v / 10 ^ j| = |(m : ℝ) - v / 10 ^ j| ∧ (c = m ∨ c % 2 = 0))) :
    Near (dv c j) (dv m j) v c := by
  have hp : (0 : ℝ) < 10 ^ j := zpow_pos (by norm_num) j
  unfold Near
  rw [abs_dv, abs_dv]
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl (mul_lt_mul_of_pos_right h hp)
  · right
    refine ⟨by rw [h], ?_⟩
    rcases h' with h' | h'
    · left; rw [h']
    · right; exact h'

theorem abs_lt_of_two (a b y : ℝ) (hab : a < b) (h : 2 * y < a + b) : |a - y| < |b - y| := by
  rcases abs_cases (a - y) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (b - y) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rw [h1, h2] <;> linarith

theorem abs_le_of_two (a b y : ℝ) (hab : a < b) (h : a + b ≤ 2 * y) : |b - y| ≤ |a - y| := by
  rcases abs_cases (a - y) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rcases abs_cases (b - y) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    rw [h1, h2] <;> linarith

/-! ### No tie across exponents -/

/-- A one-digit multiple of `10 ^ J` and a one-digit multiple of `10 ^ (J - 1)` of the interval
are never at the same distance from the value. -/
theorem no_tie (hb : WordBounds Q E nu) (hcan : E = 1 ∨ 16 ≤ Q) (J : ℤ) (c m : ℕ) (hc1 : 1 ≤ c)
    (hc9 : c ≤ 9) (hm9 : m ≤ 9) (hc : Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv c J))
    (hm : Inside (cl Q) (lo Q E nu low) (hi Q E nu) (dv m (J - 1))) :
    |dv c J - vv Q E nu| ≠ |dv m (J - 1) - vv Q E nu| := by
  intro heq
  have hp : (0 : ℝ) < 10 ^ (J - 1) := zpow_pos (by norm_num) _
  have hJ : (10 : ℝ) ^ J = 10 * 10 ^ (J - 1) := by
    rw [← zpow_one_add₀ (show (10 : ℝ) ≠ 0 by norm_num)]; congr 1; ring
  have hcJ : dv c J = (10 * c : ℝ) * 10 ^ (J - 1) := by unfold dv; rw [hJ]; ring
  have hmJ : dv m (J - 1) = (m : ℝ) * 10 ^ (J - 1) := rfl
  have hc1' : (1 : ℝ) ≤ c := by exact_mod_cast hc1
  have hm9' : (m : ℝ) ≤ 9 := by exact_mod_cast hm9
  have hlt : dv m (J - 1) < dv c J := by rw [hcJ, hmJ]; nlinarith
  -- the value is the midpoint
  have hmid : 2 * vv Q E nu = dv c J + dv m (J - 1) := by
    rcases abs_cases (dv c J - vv Q E nu) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (dv m (J - 1) - vv Q E nu) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      rw [h1, h2] at heq <;> linarith
  -- a small significand in the first binade
  have hlo := hm.lo_le
  have hhi := hc.le_hi
  have hw : hi Q E nu - lo Q E nu low ≥ (10 ^ (J - 1) : ℝ) := by
    rw [hcJ, hmJ] at *; nlinarith
  have hl9 : lo Q E nu low ≤ 9 * 10 ^ (J - 1) := by rw [hmJ] at hlo; nlinarith
  have hQ9 : Q ≤ 9 := by
    rw [width_eq hb.hQ] at hw
    unfold lo at hl9
    unfold rv at hw hl9
    have hU : (0 : ℝ) < 2 ^ (E - 1) / 2 ^ (nu + 2) := by positivity
    have h4 : ((if low then 3 else 4 : ℕ) : ℝ) ≤ 4 := by split_ifs <;> norm_num
    have hn : (nl Q low : ℝ) ≤ 36 := by
      rw [mul_div_assoc] at hw hl9
      have : (nl Q low : ℝ) * (2 ^ (E - 1) / 2 ^ (nu + 2)) ≤
          9 * (((if low then 3 else 4 : ℕ) : ℝ) * (2 ^ (E - 1) / 2 ^ (nu + 2))) := by linarith
      have : (nl Q low : ℝ) ≤ 9 * ((if low then 3 else 4 : ℕ) : ℝ) := by
        have h' : (nl Q low : ℝ) * (2 ^ (E - 1) / 2 ^ (nu + 2)) ≤
            (9 * ((if low then 3 else 4 : ℕ) : ℝ)) * (2 ^ (E - 1) / 2 ^ (nu + 2)) := by linarith
        exact le_of_mul_le_mul_right h' hU
      linarith
    have : nl Q low ≤ 36 := by exact_mod_cast hn
    unfold nl at this; split_ifs at this <;> omega
  have hE1 : E = 1 := by rcases hcan with h | h; exact h; omega
  subst hE1
  -- the exponent is far below zero
  have hv : vv Q 1 nu = (Q : ℝ) / 2 ^ nu := by
    unfold vv rv; simp only [Nat.sub_self, pow_zero, mul_one]; rw [pow_add]; push_cast
    field_simp; ring
  have hhi1 : hi Q 1 nu ≤ 38 / 2 ^ (nu + 2) := by
    unfold hi rv
    have : ((4 * Q + 2 : ℕ) : ℝ) ≤ 38 := by exact_mod_cast (by omega : 4 * Q + 2 ≤ 38)
    simp only [Nat.sub_self, pow_zero, mul_one]
    exact div_le_div_of_nonneg_right this (by positivity)
  have hnu := hb.hnu
  have hJ1 : J ≤ -2 := by
    by_contra h
    push Not at h
    have h10 : (1 / 10 : ℝ) ≤ dv c J := by
      unfold dv
      have : (10 : ℝ) ^ (-1 : ℤ) ≤ 10 ^ J := zpow_le_zpow_right₀ (by norm_num) (by omega)
      have h' : (10 : ℝ) ^ (-1 : ℤ) = 1 / 10 := by norm_num
      calc (1 / 10 : ℝ) = 10 ^ (-1 : ℤ) := h'.symm
        _ ≤ 10 ^ J := this
        _ ≤ (c : ℝ) * 10 ^ J := le_mul_of_one_le_left (zpow_pos (by norm_num) J).le hc1'
    have h2 : (38 : ℝ) / 2 ^ (nu + 2) < 1 / 10 := by
      have : (2 : ℝ) ^ (7 + 2) ≤ 2 ^ (nu + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      norm_num at this ⊢; linarith
    linarith
  -- the integer equation of the midpoint and the factor of five
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (1 : ℤ) - J = a := ⟨(1 - J).toNat, by omega⟩
  have ha3 : 3 ≤ a := by omega
  have hpow : (10 : ℝ) ^ (J - 1) = 1 / 10 ^ a := by
    rw [show J - 1 = -((a : ℤ)) by omega, zpow_neg, zpow_natCast, one_div]
  rw [hv, hcJ, hmJ, hpow] at hmid
  have hint : 2 * Q * 10 ^ a = (10 * c + m) * 2 ^ nu := by
    have h1 : (2 * Q : ℝ) / 2 ^ nu = (10 * c + m) / 10 ^ a := by
      rw [show (2 * Q : ℝ) / 2 ^ nu = 2 * (Q / 2 ^ nu) by ring, hmid]; ring
    rw [div_eq_div_iff (by positivity) (by positivity)] at h1
    exact_mod_cast h1
  have h10 : (10 : ℕ) ^ a = 2 ^ a * 5 ^ a := by rw [← mul_pow]; norm_num
  have hdvd : 5 ^ a ∣ (10 * c + m) * 2 ^ nu := by
    rw [← hint]; exact Dvd.dvd.mul_left (Dvd.intro_left _ h10.symm) _
  have hcop : Nat.Coprime (5 ^ a) (2 ^ nu) := Nat.Coprime.pow _ _ (by norm_num)
  have h5 : 5 ^ a ∣ 10 * c + m := hcop.dvd_of_dvd_mul_right hdvd
  have h5le : 5 ^ a ≤ 10 * c + m := Nat.le_of_dvd (by omega) h5
  have : 5 ^ 3 ≤ 5 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
  omega

#print axioms range_inside
#print axioms quot_half
#print axioms no_tie

end Library.Numerics.Decimal.PrintFloat.PrintFloatChoice
