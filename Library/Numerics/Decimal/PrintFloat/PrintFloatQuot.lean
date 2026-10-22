import Library.Numerics.Decimal.PrintFloat.Compiled
import Library.Numerics.Decimal.ParseFloat.ParseFloatDec
import Library.Numerics.Decimal.PrintFloat.PrintFloatShort

/-!
The printers' quotients.  `quotAt N sn sd jb` is the quotient of `num N sn j = N · 2 ^ sn · 10 ^ -j`
by `den sd j = 2 ^ sd · 10 ^ j` (one of the two powers of ten is 1) with its remainder flag, for
the decimal exponent `j = jb - 2 ^ 62` (`quotAt_spec`).  The real `N · 2 ^ sn / 2 ^ sd` lies at or
above `m · 10 ^ j` exactly when `num ≤ m · den` (`le_dv_iff`), so `range` gives the least
multiplier of `10 ^ j` in the interval and the greatest plus one (`range_spec`).  `nearest` rounds
`y` to the nearest integer, the even one at a tie, from `⌊2 y⌋` and the flag of a remainder
(`nearest_spec`), and `clamp` of that integer into a run of integers is the nearest member of the
run, with the even one at a tie (`clamp_spec`).
-/

namespace Library.Numerics.Decimal.PrintFloat.PrintFloatQuot
open PrintFloat Library.Numerics.Arithmetic.Uscale Library.Numerics.Arithmetic.Uscale.UscaleTheorem Library.Numerics.Decimal.ParseFloat.ParseFloatRound Library.Numerics.Decimal.ParseFloat.ParseFloatDec PrintFloatShort

set_option exponentiation.threshold 4096

theorem limbsOf_spec (x : UInt64) :
    Limbs (limbsOf x) ∧ val (limbsOf x) = x.toNat ∧ (limbsOf x).size = 2 := by
  have h1 := and_mask x
  have h2 := shr32 x
  have hx := x.toNat_lt
  refine ⟨?_, ?_, by simp [limbsOf, LeanExe.build]⟩
  · intro y hy
    simp [limbsOf, LeanExe.build] at hy
    rcases hy with rfl | rfl
    · rw [h1]; exact Nat.mod_lt _ (by norm_num)
    · rw [h2]
      have : x.toNat < 2 ^ 64 := hx
      omega
  · have hl : (limbsOf x).toList = [x &&& 0xFFFFFFFF, x >>> 32] := by
      simp [limbsOf, LeanExe.build, List.ofFn_succ]
    unfold val
    rw [hl]
    simp only [valL, h1, h2]
    have : x.toNat < 2 ^ 64 := hx
    omega

/-- The numerator of `N · 2 ^ sn / (2 ^ sd · 10 ^ j)`. -/
def num (N sn : ℕ) (j : ℤ) : ℕ := N * 2 ^ sn * 10 ^ (-j).toNat

/-- The denominator of `N · 2 ^ sn / (2 ^ sd · 10 ^ j)`. -/
def den (sd : ℕ) (j : ℤ) : ℕ := 2 ^ sd * 10 ^ j.toNat

theorem den_pos (sd : ℕ) (j : ℤ) : 0 < den sd j := by unfold den; positivity

theorem quotAt_spec (N sn sd jb : UInt64) (hsn : sn.toNat < 2 ^ 30) (hsd : sd.toNat < 2 ^ 30)
    (hj1 : 2 ^ 62 - 2 ^ 19 ≤ jb.toNat) (hj2 : jb.toNat ≤ 2 ^ 62 + 2 ^ 19)
    (hlt : num N.toNat sn.toNat ((jb.toNat : ℤ) - 2 ^ 62) <
      den sd.toNat ((jb.toNat : ℤ) - 2 ^ 62) * 2 ^ 63) :
    (quotAt N sn sd jb).1.toNat = num N.toNat sn.toNat ((jb.toNat : ℤ) - 2 ^ 62) /
        den sd.toNat ((jb.toNat : ℤ) - 2 ^ 62) ∧
      (quotAt N sn sd jb).2 = decide (num N.toNat sn.toNat ((jb.toNat : ℤ) - 2 ^ 62) %
        den sd.toNat ((jb.toNat : ℤ) - 2 ^ 62) ≠ 0) := by
  obtain ⟨a1, a2, a3⟩ := limbsOf_spec N
  obtain ⟨o1, o2, o3⟩ := one_limb 1 (by decide)
  unfold quotAt num den at *
  by_cases hge : jb ≥ 0x4000000000000000
  · rw [ite_eq_left hge]
    have hge' : 2 ^ 62 ≤ jb.toNat := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, bias_toNat] at hge; exact hge
    have hk : (jb - 0x4000000000000000).toNat = jb.toNat - 2 ^ 62 := by
      rw [toNat_sub' _ _ (by rw [bias_toNat]; exact hge'), bias_toNat]
    have e1 : (((jb.toNat : ℤ) - 2 ^ 62)).toNat = jb.toNat - 2 ^ 62 := by omega
    have e2 : (-((jb.toNat : ℤ) - 2 ^ 62)).toNat = 0 := by omega
    rw [e1, e2, pow_zero, mul_one] at hlt ⊢
    obtain ⟨p1, p2, p3⟩ := pow10_spec (jb - 0x4000000000000000) (by rw [hk]; omega)
    have hpow : mulPow10 (LeanExe.build 1 fun _ => (1 : UInt64)) (jb - 0x4000000000000000) =
        pow10 (jb - 0x4000000000000000) := rfl
    rw [hpow]
    obtain ⟨q1, q2⟩ := scaledQuot_spec (limbsOf N) (pow10 (jb - 0x4000000000000000)) sn sd 63
      a1 p1 (by rw [a3]; norm_num) (by rw [p3, hk]; omega) hsn hsd (by decide)
      (by rw [p2]; positivity) (by rw [a2, p2, hk, show (63 : UInt64).toNat = 63 from rfl]; linarith)
    rw [a2, p2, hk] at q1 q2
    refine ⟨by rw [q1, Nat.mul_comm (10 ^ _)], by rw [q2, Nat.mul_comm (10 ^ _)]⟩
  · rw [ite_eq_right hge]
    have hlt' : jb.toNat < 2 ^ 62 := by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, bias_toNat] at hge; omega
    have hk : (0x4000000000000000 - jb).toNat = 2 ^ 62 - jb.toNat := by
      rw [toNat_sub' _ _ (by rw [bias_toNat]; omega), bias_toNat]
    have e1 : (((jb.toNat : ℤ) - 2 ^ 62)).toNat = 0 := by omega
    have e2 : (-((jb.toNat : ℤ) - 2 ^ 62)).toNat = 2 ^ 62 - jb.toNat := by omega
    rw [e1, e2, pow_zero, mul_one] at hlt ⊢
    obtain ⟨m1, m2, m3⟩ := mulPow10_spec (limbsOf N) (0x4000000000000000 - jb) a1
      (by rw [a3]; norm_num) (by rw [hk]; omega)
    obtain ⟨q1, q2⟩ := scaledQuot_spec (mulPow10 (limbsOf N) (0x4000000000000000 - jb))
      (LeanExe.build 1 fun _ => (1 : UInt64)) sn sd 63 m1 o1 (by rw [m3, a3, hk]; omega)
      (by rw [o3]; norm_num) hsn hsd (by decide) (by rw [o2]; decide)
      (by rw [m2, o2, a2, hk, show (63 : UInt64).toNat = 63 from rfl]; simp only [UInt64.toNat_one]
          linarith)
    rw [m2, o2, a2, hk] at q1 q2
    simp only [UInt64.toNat_one, one_mul] at q1 q2
    have e3 : N.toNat * 10 ^ (2 ^ 62 - jb.toNat) * 2 ^ sn.toNat =
        N.toNat * 2 ^ sn.toNat * 10 ^ (2 ^ 62 - jb.toNat) := by ring
    rw [e3] at q1 q2
    exact ⟨q1, q2⟩

/-! ### Reals against quotients -/

/-- The real `N · 2 ^ sn / 2 ^ sd`. -/
noncomputable def rv (N sn sd : ℕ) : ℝ := (N : ℝ) * 2 ^ sn / 2 ^ sd

theorem dv_eq (m : ℕ) (j : ℤ) :
    dv m j = (m : ℝ) * 10 ^ j.toNat / 10 ^ (-j).toNat := by
  unfold dv
  have h : j = (j.toNat : ℤ) - ((-j).toNat : ℤ) := by omega
  conv_lhs => rw [h]
  rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast]
  ring

theorem le_dv_iff (N sn sd m : ℕ) (j : ℤ) :
    rv N sn sd ≤ dv m j ↔ num N sn j ≤ m * den sd j := by
  rw [dv_eq]
  unfold rv num den
  have h1 : (0 : ℝ) < 2 ^ sd := by positivity
  have h2 : (0 : ℝ) < 10 ^ (-j).toNat := by positivity
  rw [div_le_div_iff₀ h1 h2]
  constructor
  · intro h; exact_mod_cast (by push_cast; linarith : ((N * 2 ^ sn * 10 ^ (-j).toNat : ℕ) : ℝ) ≤
      ((m * (2 ^ sd * 10 ^ j.toNat) : ℕ) : ℝ))
  · intro h
    have h' : ((N * 2 ^ sn * 10 ^ (-j).toNat : ℕ) : ℝ) ≤ ((m * (2 ^ sd * 10 ^ j.toNat) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'; linarith

theorem lt_dv_iff (N sn sd m : ℕ) (j : ℤ) :
    rv N sn sd < dv m j ↔ num N sn j < m * den sd j := by
  rw [dv_eq]
  unfold rv num den
  have h1 : (0 : ℝ) < 2 ^ sd := by positivity
  have h2 : (0 : ℝ) < 10 ^ (-j).toNat := by positivity
  rw [div_lt_div_iff₀ h1 h2]
  constructor
  · intro h; exact_mod_cast (by push_cast; linarith : ((N * 2 ^ sn * 10 ^ (-j).toNat : ℕ) : ℝ) <
      ((m * (2 ^ sd * 10 ^ j.toNat) : ℕ) : ℝ))
  · intro h
    have h' : ((N * 2 ^ sn * 10 ^ (-j).toNat : ℕ) : ℝ) < ((m * (2 ^ sd * 10 ^ j.toNat) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'; linarith

/-- The quotient of the real by `10 ^ j`. -/
theorem rv_div (N sn sd : ℕ) (j : ℤ) :
    rv N sn sd / 10 ^ j = (num N sn j : ℝ) / den sd j := by
  have h := dv_eq 1 j
  unfold dv at h
  simp only [Nat.cast_one, one_mul] at h
  rw [h]
  unfold rv num den
  push_cast
  field_simp

/-! ### The range of multipliers -/

/-- The least multiplier at or above (above, for an open interval) `num / den`. -/
def ceilOf (closed : Bool) (a d : ℕ) : ℕ := if closed ∧ a % d = 0 then a / d else a / d + 1

/-- One more than the greatest multiplier at or below (below, for an open interval) `num / den`. -/
def floorOf1 (closed : Bool) (a d : ℕ) : ℕ := if ¬ closed ∧ a % d = 0 then a / d else a / d + 1

theorem ceilOf_iff (closed : Bool) (a d m : ℕ) (hd : 0 < d) :
    ceilOf closed a d ≤ m ↔ (if closed then a ≤ m * d else a < m * d) := by
  unfold ceilOf
  have hlt : a < (a / d + 1) * d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
  have hle : a / d * d ≤ a := Nat.div_mul_le_self a d
  cases closed
  · simp only [Bool.false_eq_true, false_and, ite_false]
    rw [Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hd]
  · simp only [true_and, ite_true]
    by_cases hm : a % d = 0
    · rw [ite_eq_left hm]
      have hex : a / d * d = a := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
      constructor
      · intro h; have := Nat.mul_le_mul_right d h; omega
      · intro h
        rw [← hex] at h
        exact Nat.le_of_mul_le_mul_right h hd
    · rw [ite_eq_right hm]
      constructor
      · intro h; have := Nat.mul_le_mul_right d h; omega
      · intro h
        have hne : a ≠ m * d := by
          intro he; apply hm; rw [he]; exact Nat.mul_mod_left m d
        rw [Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hd]
        omega

theorem floorOf1_iff (closed : Bool) (a d m : ℕ) (hd : 0 < d) :
    m < floorOf1 closed a d ↔ (if closed then m * d ≤ a else m * d < a) := by
  unfold floorOf1
  cases closed
  · simp only [Bool.false_eq_true, not_false_eq_true, true_and, ite_false]
    by_cases hm : a % d = 0
    · rw [ite_eq_left hm]
      have hex : a / d * d = a := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)
      constructor
      · intro h; have := Nat.mul_lt_mul_of_pos_right h hd; omega
      · intro h
        rw [← hex] at h
        exact Nat.lt_of_mul_lt_mul_right h
    · rw [ite_eq_right hm]
      have hne : m * d ≠ a := by
        intro he; apply hm; rw [← he]; exact Nat.mul_mod_left m d
      rw [Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hd]
      omega
  · simp only [not_true_eq_false, false_and, ite_false, ite_true]
    rw [Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hd]

/-- A decimal `m · 10 ^ j` lies in the interval exactly when `m` lies in the range. -/
theorem inside_iff (closed : Bool) (Nl Nh sn sd m : ℕ) (j : ℤ) :
    Inside closed (rv Nl sn sd) (rv Nh sn sd) (dv m j) ↔
      ceilOf closed (num Nl sn j) (den sd j) ≤ m ∧ m < floorOf1 closed (num Nh sn j) (den sd j) := by
  rw [ceilOf_iff _ _ _ _ (den_pos sd j), floorOf1_iff _ _ _ _ (den_pos sd j)]
  unfold Inside
  have hh : ∀ M : ℕ, dv m j ≤ rv M sn sd ↔ m * den sd j ≤ num M sn j := by
    intro M; rw [← not_lt, ← not_lt, lt_dv_iff]
  have hh' : ∀ M : ℕ, dv m j < rv M sn sd ↔ m * den sd j < num M sn j := by
    intro M; rw [← not_le, ← not_le, le_dv_iff]
  cases closed
  · simp only [Bool.false_eq_true, ite_false]
    rw [lt_dv_iff, hh']
  · simp only [ite_true]
    rw [le_dv_iff, hh]

/-- `range` computes the range of multipliers at the exponent `jb - 2 ^ 62`. -/
theorem range_spec (closed : Bool) (Nl Nh sn sd jb : UInt64) (hsn : sn.toNat < 2 ^ 30)
    (hsd : sd.toNat < 2 ^ 30) (hj1 : 2 ^ 62 - 2 ^ 19 ≤ jb.toNat) (hj2 : jb.toNat ≤ 2 ^ 62 + 2 ^ 19)
    (hl : num Nl.toNat sn.toNat ((jb.toNat : ℤ) - 2 ^ 62) <
      den sd.toNat ((jb.toNat : ℤ) - 2 ^ 62) * 2 ^ 62)
    (hh : num Nh.toNat sn.toNat ((jb.toNat : ℤ) - 2 ^ 62) <
      den sd.toNat ((jb.toNat : ℤ) - 2 ^ 62) * 2 ^ 62) :
    (range Nl Nh sn sd jb closed).1.toNat =
        ceilOf closed (num Nl.toNat sn.toNat ((jb.toNat : ℤ) - 2 ^ 62))
          (den sd.toNat ((jb.toNat : ℤ) - 2 ^ 62)) ∧
      (range Nl Nh sn sd jb closed).2.toNat =
        floorOf1 closed (num Nh.toNat sn.toNat ((jb.toNat : ℤ) - 2 ^ 62))
          (den sd.toNat ((jb.toNat : ℤ) - 2 ^ 62)) := by
  set j : ℤ := (jb.toNat : ℤ) - 2 ^ 62 with hjdef
  have hd := den_pos sd.toNat j
  obtain ⟨l1, l2⟩ := quotAt_spec Nl sn sd jb hsn hsd hj1 hj2
    (lt_of_lt_of_le hl (Nat.mul_le_mul_left _ (by norm_num)))
  obtain ⟨h1, h2⟩ := quotAt_spec Nh sn sd jb hsn hsd hj1 hj2
    (lt_of_lt_of_le hh (Nat.mul_le_mul_left _ (by norm_num)))
  rw [← hjdef] at l1 l2 h1 h2
  have ql : num Nl.toNat sn.toNat j / den sd.toNat j < 2 ^ 62 := by
    rw [Nat.div_lt_iff_lt_mul hd]; linarith
  have qh : num Nh.toNat sn.toNat j / den sd.toNat j < 2 ^ 62 := by
    rw [Nat.div_lt_iff_lt_mul hd]; linarith
  unfold range ceilOf floorOf1
  dsimp only
  constructor
  · by_cases hc : closed = true ∧ num Nl.toNat sn.toNat j % den sd.toNat j = 0
    · have hb : (closed && !(quotAt Nl sn sd jb).2) = true := by
        rw [l2, hc.1, hc.2]; decide
      rw [ite_eq_left hb, ite_eq_left hc, l1]
    · have hb : ¬ (closed && !(quotAt Nl sn sd jb).2) = true := by
        rw [l2]; intro h; apply hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_not] at h
        exact h
      rw [ite_eq_right hb, ite_eq_right hc, toNat_add' _ _ (by rw [l1]; simp; omega), l1]
      rfl
  · by_cases hc : ¬ closed = true ∧ num Nh.toNat sn.toNat j % den sd.toNat j = 0
    · have hb : (!closed && !(quotAt Nh sn sd jb).2) = true := by
        rw [h2]; simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_not]
        exact ⟨by simpa using hc.1, hc.2⟩
      rw [ite_eq_left hb, ite_eq_left hc, h1]
    · have hb : ¬ (!closed && !(quotAt Nh sn sd jb).2) = true := by
        rw [h2]; intro h; apply hc
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_not] at h
        exact ⟨by simpa using h.1, h.2⟩
      rw [ite_eq_right hb, ite_eq_right hc, toNat_add' _ _ (by rw [h1]; simp; omega), h1]
      rfl

/-! ### The nearest integer -/

/-- `near` is the nearest integer to `y`, the even one at a tie. -/
def NearestInt (y : ℝ) (near : ℕ) : Prop :=
  ∀ m : ℕ, |(near : ℝ) - y| < |(m : ℝ) - y| ∨
    (|(near : ℝ) - y| = |(m : ℝ) - y| ∧ (near = m ∨ near % 2 = 0))

/-- Two distinct integers lie at least 1 apart. -/
theorem one_le_abs (m c : ℕ) (h : m ≠ c) : 1 ≤ |(m : ℝ) - c| := by
  rcases lt_or_gt_of_ne h with h' | h'
  · have : (m : ℝ) + 1 ≤ c := by exact_mod_cast h'
    rw [abs_of_neg (by linarith)]; linarith
  · have : (c : ℝ) + 1 ≤ m := by exact_mod_cast h'
    rw [abs_of_pos (by linarith)]; linarith

theorem dist_ge (m c : ℕ) (y : ℝ) (h : m ≠ c) : 1 - |(c : ℝ) - y| ≤ |(m : ℝ) - y| := by
  have h1 := one_le_abs m c h
  have h2 : |(m : ℝ) - c| ≤ |(m : ℝ) - y| + |(c : ℝ) - y| := by
    have := abs_sub_le (m : ℝ) y c
    rwa [abs_sub_comm y c] at this
  linarith

/-- An integer within less than one half of `y` is its nearest. -/
theorem nearest_of_lt (c : ℕ) (y : ℝ) (h : |(c : ℝ) - y| < 1 / 2) : NearestInt y c := by
  intro m
  by_cases hm : m = c
  · right; rw [hm]; exact ⟨rfl, Or.inl rfl⟩
  · left; have := dist_ge m c y hm; linarith

/-- An even integer at one half from `y` is its nearest, the even one at the tie. -/
theorem nearest_of_tie (c : ℕ) (y : ℝ) (h : |(c : ℝ) - y| = 1 / 2) (he : c % 2 = 0) :
    NearestInt y c := by
  intro m
  by_cases hm : m = c
  · right; rw [hm]; exact ⟨rfl, Or.inl rfl⟩
  · have := dist_ge m c y hm
    rcases lt_or_eq_of_le (show |(c : ℝ) - y| ≤ |(m : ℝ) - y| by linarith) with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', Or.inr he⟩

theorem nearest_spec (y : ℝ) (f2 : UInt64) (r2 : Bool) (hf : f2.toNat < 2 ^ 63)
    (h1 : (f2.toNat : ℝ) ≤ 2 * y) (h2 : 2 * y < f2.toNat + 1)
    (hr : r2 = decide ((f2.toNat : ℝ) ≠ 2 * y)) :
    NearestInt y (nearest f2 r2).toNat := by
  have hlow : (f2 &&& 1).toNat = f2.toNat % 2 := by
    rw [UInt64.toNat_and, show (1 : UInt64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hhalf : (f2 >>> 1).toNat = f2.toNat / 2 := by
    rw [UInt64.toNat_shiftRight, show (1 : UInt64).toNat % 64 = 1 from rfl, Nat.shiftRight_eq_div_pow]
  obtain ⟨a, ha⟩ : ∃ a, a = f2.toNat / 2 := ⟨_, rfl⟩
  rw [← ha] at hhalf
  have hf2 : f2.toNat = 2 * a + f2.toNat % 2 := by omega
  unfold nearest
  by_cases hb : f2.toNat % 2 = 0
  · have hb' : (f2 &&& 1 == 0) = true := by
      rw [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hlow, hb]; rfl
    rw [ite_eq_left hb', hhalf]
    have e : (f2.toNat : ℝ) = 2 * a := by rw [hf2, hb]; push_cast; ring
    apply nearest_of_lt
    rw [abs_lt]; constructor <;> linarith
  · have hb1 : f2.toNat % 2 = 1 := by omega
    have hb' : ¬ (f2 &&& 1 == 0) = true := by
      rw [beq_iff_eq]; intro h; have := congrArg UInt64.toNat h; rw [hlow] at this
      simp at this; omega
    rw [ite_eq_right hb']
    have e : (f2.toNat : ℝ) = 2 * a + 1 := by rw [hf2, hb1]; push_cast; ring
    by_cases hr2 : r2 = true
    · rw [ite_eq_left hr2, toNat_add' _ _ (by rw [hhalf]; simp; omega), hhalf]
      simp only [UInt64.toNat_one]
      have hne : (f2.toNat : ℝ) ≠ 2 * y := by rw [hr] at hr2; exact of_decide_eq_true hr2
      have hy : (a : ℝ) + 1 / 2 < y := by
        rcases lt_or_eq_of_le (show (a : ℝ) + 1 / 2 ≤ y by linarith) with h | h
        · exact h
        · exfalso; apply hne; rw [e]; linarith
      apply nearest_of_lt
      push_cast
      rw [abs_lt]; constructor <;> linarith
    · rw [ite_eq_right hr2]
      have heq : y = (a : ℝ) + 1 / 2 := by
        have : ¬ (f2.toNat : ℝ) ≠ 2 * y := by
          intro h; apply hr2; rw [hr]; exact decide_eq_true h
        push Not at this
        linarith
      by_cases he : ((f2 >>> 1) &&& 1 == 0) = true
      · rw [ite_eq_left he, hhalf]
        apply nearest_of_tie
        · rw [heq, show (a : ℝ) - (a + 1 / 2) = -(1 / 2) by ring, abs_neg, abs_of_pos (by norm_num)]
        · have := congrArg UInt64.toNat (beq_iff_eq.mp he)
          rw [UInt64.toNat_and, show (1 : UInt64).toNat = 2 ^ 1 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod, hhalf] at this
          simpa using this
      · rw [ite_eq_right he, toNat_add' _ _ (by rw [hhalf]; simp; omega), hhalf]
        simp only [UInt64.toNat_one]
        apply nearest_of_tie
        · push_cast
          rw [heq, show (a : ℝ) + 1 - (a + 1 / 2) = 1 / 2 by ring, abs_of_pos (by norm_num)]
        · have : ¬ ((f2 >>> 1) &&& 1) = 0 := fun h => he (beq_iff_eq.mpr h)
          have h' : ((f2 >>> 1) &&& 1).toNat ≠ 0 := fun h => this (UInt64.toNat_inj.mp h)
          rw [UInt64.toNat_and, show (1 : UInt64).toNat = 2 ^ 1 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod, hhalf] at h'
          omega

/-- The nearest integer lies within one half. -/
theorem nearest_half (y : ℝ) (hy : 0 ≤ y) (c : ℕ) (hc : NearestInt y c) : |(c : ℝ) - y| ≤ 1 / 2 := by
  set r := Nat.floor (y + 1 / 2) with hr
  have h1 : (r : ℝ) ≤ y + 1 / 2 := Nat.floor_le (by linarith)
  have h2 : y + 1 / 2 < r + 1 := Nat.lt_floor_add_one _
  have hr' : |(r : ℝ) - y| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  rcases hc r with h | ⟨h, _⟩ <;> linarith

/-- The clamp of the nearest integer into the run `[lo, hi1)` is the nearest member of the run. -/
theorem clamp_spec (y : ℝ) (hy : 0 ≤ y) (near lo hi1 : UInt64) (hn : NearestInt y near.toNat)
    (hrun : lo.toNat < hi1.toNat) (hn1 : near.toNat < 2 ^ 63) :
    lo.toNat ≤ (clamp near lo hi1).toNat ∧ (clamp near lo hi1).toNat < hi1.toNat ∧
      ∀ m : ℕ, lo.toNat ≤ m → m < hi1.toNat →
        |((clamp near lo hi1).toNat : ℝ) - y| < |(m : ℝ) - y| ∨
        (|((clamp near lo hi1).toNat : ℝ) - y| = |(m : ℝ) - y| ∧
          ((clamp near lo hi1).toNat = m ∨ (clamp near lo hi1).toNat % 2 = 0)) := by
  have hhalf := nearest_half y hy _ hn
  have hab := abs_le.mp hhalf
  unfold clamp
  by_cases h1 : near < lo
  · rw [ite_eq_left h1]
    have h1' : near.toNat < lo.toNat := UInt64.lt_iff_toNat_lt.mp h1
    refine ⟨le_rfl, hrun, ?_⟩
    have hy' : y ≤ (lo.toNat : ℝ) - 1 / 2 := by
      have : (near.toNat : ℝ) + 1 ≤ lo.toNat := by exact_mod_cast h1'
      linarith
    intro m hm1 _
    rcases eq_or_lt_of_le hm1 with h | h
    · right; rw [h]; exact ⟨rfl, Or.inl rfl⟩
    · left
      have : (lo.toNat : ℝ) + 1 ≤ m := by exact_mod_cast h
      rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]
      linarith
  · rw [ite_eq_right h1]
    have h1' : lo.toNat ≤ near.toNat := by
      have := UInt64.lt_iff_toNat_lt.not.mp h1; omega
    by_cases h2 : near + 1 > hi1
    · rw [ite_eq_left h2]
      have h2' : hi1.toNat ≤ near.toNat := by
        have := UInt64.lt_iff_toNat_lt.mp h2
        rw [toNat_add' _ _ (by simp; omega)] at this; simp at this; omega
      have hs : (hi1 - 1).toNat = hi1.toNat - 1 := by
        rw [toNat_sub' _ _ (by simp; omega)]; simp
      rw [hs]
      refine ⟨by omega, by omega, ?_⟩
      have hy' : (hi1.toNat : ℝ) - 1 / 2 ≤ y := by
        have : (hi1.toNat : ℝ) ≤ near.toNat := by exact_mod_cast h2'
        linarith
      have ec : ((hi1.toNat - 1 : ℕ) : ℝ) = (hi1.toNat : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      intro m _ hm2
      rcases eq_or_lt_of_le (show m ≤ hi1.toNat - 1 by omega) with h | h
      · right; rw [h]; exact ⟨rfl, Or.inl rfl⟩
      · left
        have : (m : ℝ) + 1 ≤ ((hi1.toNat - 1 : ℕ) : ℝ) := by exact_mod_cast h
        rw [ec] at this ⊢
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
        linarith
    · rw [ite_eq_right h2]
      have h2' : near.toNat < hi1.toNat := by
        have := UInt64.lt_iff_toNat_lt.not.mp h2
        rw [toNat_add' _ _ (by simp; omega)] at this; simp at this; omega
      exact ⟨h1', h2', fun m _ _ => hn m⟩

#print axioms limbsOf_spec
#print axioms quotAt_spec
#print axioms inside_iff
#print axioms range_spec
#print axioms nearest_spec
#print axioms clamp_spec

end Library.Numerics.Decimal.PrintFloat.PrintFloatQuot
