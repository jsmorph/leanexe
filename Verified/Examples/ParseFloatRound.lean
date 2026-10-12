import Verified.Examples.ParseFloat
import Verified.Examples.UscaleArith
import Verified.Examples.StrconvGrid
import Verified.Examples.StrconvOfScientific

/-!
`ParseFloat.roundUnits` rounds an unrounded quotient to the nearest-even encoding.  Its arguments
describe the real `y = (u + φ) · 2 ^ (T - 2 ^ 62)` in units of the least subnormal, where `T` is the
word `tb`, `φ` lies in `[0, 1)`, and the flag `sticky` states `φ > 0`.  `round_shift` proves the
rounding of `(u + φ) / 2 ^ r` from the dropped bits `u % 2 ^ r` and the flag: up above half, down
below half, and at exactly half up when `φ > 0` or the kept part is odd.  `roundUnits_spec` proves
that the result is `StrconvGrid.refPos f y` when the flag is set only for a `u` of at least `p + 2`
bits, which guarantees that at least two bits are dropped, so that the flag decides every tie.
-/

namespace Verified.Examples.ParseFloatRound
open ParseFloat Uscale UscaleTheorem StrconvGrid

set_option exponentiation.threshold 4096

/-- The nearest-even rounding of `(u + φ) / 2 ^ r` from the dropped bits and the flag of `φ`. -/
theorem round_shift (u r : ℕ) (hr : 1 ≤ r) (φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ < 1) (Q : ℕ)
    (hQ : Q = if 2 ^ (r - 1) < u % 2 ^ r ∨
        (u % 2 ^ r = 2 ^ (r - 1) ∧ (0 < φ ∨ u / 2 ^ r % 2 = 1)) then u / 2 ^ r + 1
      else u / 2 ^ r) :
    2 * ((u : ℝ) + φ) ≤ (2 * Q + 1) * 2 ^ r ∧ 2 * (Q : ℝ) * 2 ^ r ≤ 2 * ((u : ℝ) + φ) + 2 ^ r ∧
      (2 * ((u : ℝ) + φ) = (2 * Q + 1) * 2 ^ r ∨ 2 * ((u : ℝ) + φ) + 2 ^ r = 2 * Q * 2 ^ r →
        Q % 2 = 0) := by
  set H := 2 ^ (r - 1) with hH
  have hR : (2 : ℕ) ^ r = 2 * H := by rw [hH, ← pow_succ']; congr 1; omega
  have hH1 : 1 ≤ H := Nat.one_le_two_pow
  set q0 := u / 2 ^ r with hq0
  set rem := u % 2 ^ r with hrem
  have hu : u = q0 * (2 * H) + rem := by rw [hq0, hrem, ← hR]; exact (Nat.div_add_mod' u _).symm
  have hrl : rem < 2 * H := by rw [hrem, ← hR]; exact Nat.mod_lt _ (by positivity)
  have hRr : (2 : ℝ) ^ r = 2 * (H : ℝ) := by exact_mod_cast hR
  have hur : (u : ℝ) = q0 * (2 * H) + rem := by exact_mod_cast hu
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH1
  rw [hRr, hur]
  by_cases hup : H < rem ∨ (rem = H ∧ (0 < φ ∨ q0 % 2 = 1))
  · rw [if_pos hup] at hQ
    subst hQ
    push_cast
    rcases hup with h | ⟨h, h'⟩
    · have h2 : (H : ℝ) + 1 ≤ rem := by exact_mod_cast h
      have h3 : (rem : ℝ) + 1 ≤ 2 * H := by exact_mod_cast hrl
      refine ⟨by nlinarith, by nlinarith, fun ht => ?_⟩
      exfalso; rcases ht with ht | ht <;> nlinarith
    · have h2 : (rem : ℝ) = H := by exact_mod_cast h
      refine ⟨by nlinarith, by nlinarith, fun ht => ?_⟩
      rcases ht with ht | ht
      · exfalso; nlinarith
      · have hφ : φ = 0 := by nlinarith
        rcases h' with h' | h'
        · exfalso; linarith
        · omega
  · rw [if_neg hup] at hQ
    subst hQ
    push Not at hup
    obtain ⟨hle, hne⟩ := hup
    have hle' : (rem : ℝ) ≤ H := by exact_mod_cast hle
    by_cases heq : rem = H
    · obtain ⟨hφ, hodd⟩ := hne heq
      have hφ0 : φ = 0 := le_antisymm hφ h0
      subst hφ0
      have h2 : (rem : ℝ) = H := by exact_mod_cast heq
      refine ⟨by nlinarith, by nlinarith, fun _ => by omega⟩
    · have hlt : rem + 1 ≤ H := by omega
      have h2 : (rem : ℝ) + 1 ≤ H := by exact_mod_cast hlt
      refine ⟨by nlinarith, by nlinarith, fun ht => ?_⟩
      exfalso; rcases ht with ht | ht <;> nlinarith

/-! ### Words -/

theorem shl1 (j : UInt64) (hj : j.toNat < 64) : ((1 : UInt64) <<< j).toNat = 2 ^ j.toNat := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hj, show (1 : UInt64).toNat = 1 from rfl,
    Nat.shiftLeft_eq, one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) hj)

theorem shr (u j : UInt64) (hj : j.toNat < 64) : (u >>> j).toNat = u.toNat / 2 ^ j.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hj, Nat.shiftRight_eq_div_pow]

theorem low_bits (u j : UInt64) (hj : j.toNat < 64) :
    (u &&& (((1 : UInt64) <<< j) - 1)).toNat = u.toNat % 2 ^ j.toNat := by
  rw [UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ (by
    rw [UInt64.le_iff_toNat_le, shl1 j hj]; exact Nat.one_le_two_pow), shl1 j hj,
    show (1 : UInt64).toNat = 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem shl_word (u k : UInt64) (hk : k.toNat < 64) (h : u.toNat * 2 ^ k.toNat < 2 ^ 64) :
    (u <<< k).toNat = u.toNat * 2 ^ k.toNat := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem toNat_sub' (a b : UInt64) (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h)

theorem toNat_add' (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_mul' (a b : UInt64) (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h]

theorem bias_toNat : (0x4000000000000000 : UInt64).toNat = 2 ^ 62 := rfl

/-! ### The significand -/

/-- The significand of `roundUnits` when `R` bits are dropped. -/
def qDrop (u : UInt64) (sticky : Bool) (R : UInt64) : UInt64 :=
  if R == 0 then u
  else if R ≥ 64 then 0
  else if ((1 : UInt64) <<< (R - 1)) < (u &&& (((1 : UInt64) <<< R) - 1)) ||
      ((u &&& (((1 : UInt64) <<< R) - 1)) == ((1 : UInt64) <<< (R - 1)) &&
        (sticky || (u >>> R) &&& 1 == 1)) then (u >>> R) + 1
  else u >>> R

/-- The significand that `roundUnits` computes in the binade of field `e`. -/
def qOf (u : UInt64) (sticky : Bool) (tb e : UInt64) : UInt64 :=
  if tb ≤ e - 1 + 0x4000000000000000 then qDrop u sticky (e - 1 + 0x4000000000000000 - tb)
  else u <<< (tb - 0x4000000000000000 - (e - 1))

theorem roundUnits_eq (p F u : UInt64) (sticky : Bool) (tb : UInt64) :
    roundUnits p F u sticky tb =
      if u == 0 then 0
      else
        let e := if wordBits u + tb ≤ p + 0x4000000000000000 then 1
          else wordBits u + tb - 0x4000000000000000 - p + 1
        if e ≥ F then F <<< (p - 1)
        else if (e - 1) * ((1 : UInt64) <<< (p - 1)) + qOf u sticky tb e ≥ F <<< (p - 1) then
          F <<< (p - 1)
        else (e - 1) * ((1 : UInt64) <<< (p - 1)) + qOf u sticky tb e := rfl

/-- In a binade whose shift `r = E - 1 + 2 ^ 62 - T` drops bits, `qOf` rounds `(u + φ) / 2 ^ r`
to nearest with ties to even. -/
theorem qOf_drop (u e tb : UInt64) (sticky : Bool) (φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ < 1)
    (hs : sticky = decide (0 < φ)) (hu : u.toNat < 2 ^ 63)
    (he : e.toNat < 2 ^ 62) (he1 : 1 ≤ e.toNat) (hT : tb.toNat ≤ e.toNat - 1 + 2 ^ 62)
    (r : ℕ) (hrdef : r = e.toNat - 1 + 2 ^ 62 - tb.toNat) (hr0 : sticky = true → 1 ≤ r)
    (Q : ℕ) (hQ : Q = (qOf u sticky tb e).toNat) :
    Q < 2 ^ 63 ∧
    2 * ((u.toNat : ℝ) + φ) ≤ (2 * Q + 1) * 2 ^ r ∧
      2 * (Q : ℝ) * 2 ^ r ≤ 2 * ((u.toNat : ℝ) + φ) + 2 ^ r ∧
      (2 * ((u.toNat : ℝ) + φ) = (2 * Q + 1) * 2 ^ r ∨
        2 * ((u.toNat : ℝ) + φ) + 2 ^ r = 2 * Q * 2 ^ r → Q % 2 = 0) := by
  have he1w : (e - 1).toNat = e.toNat - 1 := toNat_sub' e 1 (by simpa using he1)
  have hsum : (e - 1 + 0x4000000000000000).toNat = e.toNat - 1 + 2 ^ 62 := by
    rw [toNat_add' _ _ (by rw [he1w, bias_toNat]; omega), he1w, bias_toNat]
  have hcond : tb ≤ e - 1 + 0x4000000000000000 := by
    rw [UInt64.le_iff_toNat_le, hsum]; exact hT
  have hrw : (e - 1 + 0x4000000000000000 - tb).toNat = r := by
    rw [toNat_sub' _ _ (by rw [hsum]; exact hT), hsum, hrdef]
  have hQdef : qOf u sticky tb e = qDrop u sticky (e - 1 + 0x4000000000000000 - tb) := by
    unfold qOf; rw [if_pos hcond]
  generalize e - 1 + 0x4000000000000000 - tb = R at hrw hQdef
  rw [hQdef] at hQ
  clear hQdef hcond hsum he1w hrdef
  unfold qDrop at hQ
  by_cases hr : r = 0
  · -- nothing dropped: `φ = 0`
    have hst : sticky = false := by
      cases hsc : sticky
      · rfl
      · exact absurd (hr0 hsc) (by omega)
    have hφ : φ = 0 := by
      rw [hst] at hs
      have := of_decide_eq_false hs.symm
      linarith
    subst hφ
    have hR0 : (R == 0) = true := by
      simp only [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [hrw, hr]; rfl
    rw [if_pos hR0] at hQ
    rw [hQ, hr]
    refine ⟨hu, by simp <;> linarith, by simp <;> linarith, fun ht => ?_⟩
    exfalso; simp at ht
  have hR0 : (R == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hr; rw [← hrw, h]; rfl
  rw [if_neg (by simp [hR0])] at hQ
  by_cases h64 : 64 ≤ r
  · have hR64 : R ≥ 64 := UInt64.le_iff_toNat_le.mpr (by rw [hrw]; exact h64)
    rw [if_pos hR64] at hQ
    rw [hQ]
    have hp : (2 : ℝ) ^ 64 ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) h64
    have hu' : (u.toNat : ℝ) + 1 ≤ 2 ^ 63 := by exact_mod_cast hu
    refine ⟨by norm_num, by push_cast; nlinarith, by push_cast; nlinarith, fun ht => ?_⟩
    exfalso; push_cast at ht; rcases ht with ht | ht <;> nlinarith
  · push Not at h64
    have hR64 : ¬ R ≥ 64 := fun h => by
      have := UInt64.le_iff_toNat_le.mp h; rw [hrw] at this; simp at this; omega
    rw [if_neg hR64] at hQ
    have hr1 : 1 ≤ r := by omega
    have hRw : R.toNat < 64 := by rw [hrw]; exact h64
    have hR1 : (R - 1).toNat = r - 1 := by
      rw [toNat_sub' _ _ (by rw [hrw, UInt64.toNat_one]; exact hr1), hrw, UInt64.toNat_one]
    have hlow := low_bits u R hRw
    have hhalf := shl1 (R - 1) (by rw [hR1]; omega)
    have hdiv := shr u R hRw
    rw [hrw] at hlow hdiv
    rw [hR1] at hhalf
    have hodd : ((u >>> R) &&& 1 == 1) = decide (u.toNat / 2 ^ r % 2 = 1) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← hdiv]
      constructor
      · intro h; have := congrArg UInt64.toNat h
        rw [UInt64.toNat_and] at this; simpa [Nat.and_one_is_mod] using this
      · intro h; apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_and]; simpa [Nat.and_one_is_mod] using h
    have hcond' : (((1 : UInt64) <<< (R - 1)) < (u &&& (((1 : UInt64) <<< R) - 1)) ||
        ((u &&& (((1 : UInt64) <<< R) - 1)) == ((1 : UInt64) <<< (R - 1)) &&
          (sticky || (u >>> R) &&& 1 == 1))) =
        decide (2 ^ (r - 1) < u.toNat % 2 ^ r ∨
          (u.toNat % 2 ^ r = 2 ^ (r - 1) ∧ (0 < φ ∨ u.toNat / 2 ^ r % 2 = 1))) := by
      have e1 : decide (((1 : UInt64) <<< (R - 1)) < (u &&& (((1 : UInt64) <<< R) - 1))) =
          decide (2 ^ (r - 1) < u.toNat % 2 ^ r) := by
        simp only [decide_eq_decide, UInt64.lt_iff_toNat_lt, hhalf, hlow]
      have e2 : ((u &&& (((1 : UInt64) <<< R) - 1)) == ((1 : UInt64) <<< (R - 1))) =
          decide (u.toNat % 2 ^ r = 2 ^ (r - 1)) := by
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
        constructor
        · intro h; have := congrArg UInt64.toNat h; rw [hlow, hhalf] at this; exact this
        · intro h; apply UInt64.toNat_inj.mp; rw [hlow, hhalf]; exact h
      rw [e1, e2, hodd, hs]
      simp only [Bool.decide_or, Bool.decide_and]
    rw [hcond'] at hQ
    have hq0 : u.toNat / 2 ^ r < 2 ^ 62 := by
      have : u.toNat / 2 ^ r ≤ u.toNat / 2 := Nat.div_le_div_left
        (by calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr1) (by norm_num)
      omega
    have hQ' : Q = if 2 ^ (r - 1) < u.toNat % 2 ^ r ∨
        (u.toNat % 2 ^ r = 2 ^ (r - 1) ∧ (0 < φ ∨ u.toNat / 2 ^ r % 2 = 1)) then
        u.toNat / 2 ^ r + 1 else u.toNat / 2 ^ r := by
      rw [hQ]
      by_cases hc : 2 ^ (r - 1) < u.toNat % 2 ^ r ∨
          (u.toNat % 2 ^ r = 2 ^ (r - 1) ∧ (0 < φ ∨ u.toNat / 2 ^ r % 2 = 1))
      · rw [if_pos (decide_eq_true hc), if_pos hc,
          toNat_add' _ _ (by rw [hdiv, UInt64.toNat_one]; omega), hdiv, UInt64.toNat_one]
      · rw [if_neg (by simpa using hc), if_neg hc, hdiv]
    obtain ⟨a1, a2, a3⟩ := round_shift u.toNat r hr1 φ h0 h1 Q hQ'
    refine ⟨?_, a1, a2, a3⟩
    rw [hQ']
    split_ifs <;> omega

/-! ### The rounding -/

theorem two_zpow_split (a b : ℕ) (c : ℤ) (h : (a : ℤ) = b + c) :
    (2 : ℝ) ^ a = 2 ^ b * (2 : ℝ) ^ c := by
  rw [← zpow_natCast, h, zpow_add₀ two_ne_zero, zpow_natCast]

/-- `roundUnits` gives the nearest-even encoding of `(u + φ) · 2 ^ (T - 2 ^ 62)` units. -/
theorem roundUnits_spec (f : Fmt) (p F u tb : UInt64) (sticky : Bool) (φ : ℝ)
    (hp : p.toNat = f.p) (hF : F.toNat = f.F) (hp60 : f.p ≤ 60)
    (hlim : f.F * 2 ^ (f.p - 1) < 2 ^ 62)
    (hu : u.toNat < 2 ^ 63) (hT1 : 2 ^ 61 ≤ tb.toNat) (hT2 : tb.toNat ≤ 2 ^ 62 + 2 ^ 61)
    (h0 : 0 ≤ φ) (h1 : φ < 1) (hs : sticky = decide (0 < φ))
    (hsb : sticky = true → f.p + 2 ≤ Nat.size u.toNat) :
    (roundUnits p F u sticky tb).toNat =
      refPos f (((u.toNat : ℝ) + φ) * (2 : ℝ) ^ ((tb.toNat : ℤ) - 2 ^ 62)) := by
  have hfp := f.hp
  have hfF := f.hF
  have hF62 : f.F < 2 ^ 62 := by
    have : 1 ≤ 2 ^ (f.p - 1) := Nat.one_le_two_pow
    nlinarith
  set T := tb.toNat with hTdef
  set t : ℤ := (T : ℤ) - 2 ^ 62 with htdef
  have ht2 : (0 : ℝ) < (2 : ℝ) ^ t := zpow_pos (by norm_num) t
  rw [roundUnits_eq]
  by_cases hu0 : u.toNat = 0
  · have hst : sticky = false := by
      cases hsc : sticky
      · rfl
      · have := hsb hsc; rw [hu0, Nat.size_zero] at this; omega
    have hφ : φ = 0 := by
      rw [hst] at hs; have := of_decide_eq_false hs.symm; linarith
    have hu0' : (u == 0) = true := by
      simp only [beq_iff_eq]; exact UInt64.toNat_inj.mp (by rw [hu0]; rfl)
    rw [if_pos hu0', hu0, hφ]
    simp only [Nat.cast_zero, add_zero, zero_mul]
    rw [StrconvOfScientific.refPos_small f 0 le_rfl (by norm_num)]
    rfl
  have hu0' : (u == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hu0; rw [h]; rfl
  rw [if_neg (by simp [hu0'])]
  dsimp only
  set n := Nat.size u.toNat with hndef
  have hwb : (wordBits u).toNat = n := UscaleTheorem.wordBits_spec u
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (fun h => hu0 (Nat.size_eq_zero.mp h))
  have hn63 : n ≤ 63 := Nat.size_le.mpr hu
  have hun1 : 2 ^ (n - 1) ≤ u.toNat := Nat.lt_size.mp (by omega)
  have hun2 : u.toNat < 2 ^ n := Nat.lt_size_self _
  -- the binade
  set E : ℕ := if n + T ≤ f.p + 2 ^ 62 then 1 else n + T - 2 ^ 62 - f.p + 1 with hEdef
  have hE : (if wordBits u + tb ≤ p + 0x4000000000000000 then (1 : UInt64)
      else wordBits u + tb - 0x4000000000000000 - p + 1).toNat = E := by
    have hsum : (wordBits u + tb).toNat = n + T := by rw [toNat_add' _ _ (by omega), hwb]
    have hpb : (p + 0x4000000000000000).toNat = f.p + 2 ^ 62 := by
      rw [toNat_add' _ _ (by rw [hp, bias_toNat]; omega), hp, bias_toNat]
    by_cases hc : n + T ≤ f.p + 2 ^ 62
    · rw [if_pos (UInt64.le_iff_toNat_le.mpr (by rw [hsum, hpb]; exact hc))]
      rw [hEdef, if_pos hc]; rfl
    · rw [if_neg (fun h => hc (by have := UInt64.le_iff_toNat_le.mp h; rwa [hsum, hpb] at this))]
      rw [hEdef, if_neg hc]
      have h1' : (wordBits u + tb - 0x4000000000000000).toNat = n + T - 2 ^ 62 := by
        rw [toNat_sub' _ _ (by rw [hsum, bias_toNat]; omega), hsum, bias_toNat]
      have h2' : (wordBits u + tb - 0x4000000000000000 - p).toNat = n + T - 2 ^ 62 - f.p := by
        rw [toNat_sub' _ _ (by rw [h1', hp]; omega), h1', hp]
      rw [toNat_add' _ _ (by rw [h2']; simp; omega), h2']; rfl
  generalize hew : (if wordBits u + tb ≤ p + 0x4000000000000000 then (1 : UInt64)
      else wordBits u + tb - 0x4000000000000000 - p + 1) = e at hE
  have hE1 : 1 ≤ E := by rw [hEdef]; split_ifs <;> omega
  -- the value's place in its binade
  set y : ℝ := ((u.toNat : ℝ) + φ) * (2 : ℝ) ^ t with hydef
  have hupper : y < (2 : ℝ) ^ f.p * 2 ^ (E - 1) := by
    have hu1 : (u.toNat : ℝ) + φ < 2 ^ n := by
      have : (u.toNat : ℝ) + 1 ≤ 2 ^ n := by exact_mod_cast hun2
      linarith
    have hy : y < 2 ^ n * (2 : ℝ) ^ t := mul_lt_mul_of_pos_right hu1 ht2
    by_cases hc : n + T ≤ f.p + 2 ^ 62
    · have hE1' : E = 1 := by rw [hEdef, if_pos hc]
      rw [hE1', Nat.sub_self, pow_zero, mul_one]
      calc y < 2 ^ n * (2 : ℝ) ^ t := hy
        _ = (2 : ℝ) ^ ((n : ℤ) + t) := by rw [zpow_add₀ two_ne_zero, zpow_natCast]
        _ ≤ (2 : ℝ) ^ (f.p : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
        _ = 2 ^ f.p := zpow_natCast _ _
    · have hE' : E - 1 = n + T - 2 ^ 62 - f.p := by rw [hEdef, if_neg hc]; omega
      calc y < 2 ^ n * (2 : ℝ) ^ t := hy
        _ = 2 ^ f.p * 2 ^ (E - 1) := by
          rw [← pow_add, two_zpow_split (f.p + (E - 1)) n t (by omega)]
  have hlower : E = 1 ∨ (2 : ℝ) ^ (f.p - 1) * 2 ^ (E - 1) ≤ y := by
    by_cases hc : n + T ≤ f.p + 2 ^ 62
    · left; rw [hEdef, if_pos hc]
    · right
      have hE' : E - 1 = n + T - 2 ^ 62 - f.p := by rw [hEdef, if_neg hc]; omega
      have hu1 : (2 : ℝ) ^ (n - 1) ≤ (u.toNat : ℝ) + φ := by
        have : ((2 ^ (n - 1) : ℕ) : ℝ) ≤ u.toNat := by exact_mod_cast hun1
        push_cast at this; linarith
      calc (2 : ℝ) ^ (f.p - 1) * 2 ^ (E - 1) = 2 ^ (n - 1) * (2 : ℝ) ^ t := by
            rw [← pow_add, two_zpow_split (f.p - 1 + (E - 1)) (n - 1) t (by omega)]
        _ ≤ y := mul_le_mul_of_nonneg_right hu1 ht2.le
  by_cases hEF : f.F ≤ E
  · -- beyond the finite binades
    rw [if_pos (UInt64.le_iff_toNat_le.mpr (by rw [hE, hF]; exact hEF))]
    have hpw : ((1 : UInt64) <<< (p - 1)).toNat = 2 ^ (f.p - 1) := by
      rw [shl1 _ (by rw [toNat_sub' _ _ (by rw [hp]; simp; omega), hp]; simp; omega),
        toNat_sub' _ _ (by rw [hp]; simp; omega), hp]; rfl
    have hFs : (F <<< (p - 1)).toNat = limit f := by
      rw [shl_word _ _ (by rw [toNat_sub' _ _ (by rw [hp]; simp; omega), hp]; simp; omega)
        (by rw [toNat_sub' _ _ (by rw [hp]; simp; omega), hp, hF]; simp; omega),
        toNat_sub' _ _ (by rw [hp]; simp; omega), hp, hF]
      unfold limit half; simp
    rw [hFs]
    symm
    unfold refPos
    rw [if_pos]
    rcases hlower with h | h
    · omega
    · refine le_trans ?_ h
      rw [threshold_eq]
      have hh : (half f : ℝ) = 2 ^ (f.p - 1) := by unfold half; push_cast; ring
      rw [hh]
      have h3 : (2 : ℝ) ^ (f.F - 3) * 4 ≤ 2 ^ (E - 1) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h4 : (0 : ℝ) ≤ 2 ^ (f.F - 3) := by positivity
      have h5 : (0 : ℝ) < 2 ^ (f.p - 1) := by positivity
      nlinarith
  rw [if_neg (fun h => hEF (by have := UInt64.le_iff_toNat_le.mp h; rwa [hE, hF] at this))]
  push Not at hEF
  have hpw : ((1 : UInt64) <<< (p - 1)).toNat = 2 ^ (f.p - 1) := by
    have h1' : (p - 1).toNat = f.p - 1 := by rw [toNat_sub' _ _ (by rw [hp]; simp; omega), hp]; rfl
    rw [shl1 _ (by rw [h1']; omega), h1']
  have hFs : (F <<< (p - 1)).toNat = limit f := by
    have h1' : (p - 1).toNat = f.p - 1 := by rw [toNat_sub' _ _ (by rw [hp]; simp; omega), hp]; rfl
    rw [shl_word _ _ (by rw [h1']; omega) (by rw [h1', hF]; omega), h1', hF]
    unfold limit half; rfl
  have he1w : (e - 1).toNat = E - 1 := by
    rw [toNat_sub' _ _ (by rw [UInt64.toNat_one, hE]; exact hE1), hE]; rfl
  set Q := (qOf u sticky tb e).toNat with hQdef
  have hR : RoundsTo f y E Q := by
    by_cases hd : T ≤ E - 1 + 2 ^ 62
    · set r := E - 1 + 2 ^ 62 - T with hrdef
      have hr0 : sticky = true → 1 ≤ r := by
        intro hsc
        have := hsb hsc
        by_cases hc : n + T ≤ f.p + 2 ^ 62
        · have : E = 1 := by rw [hEdef, if_pos hc]
          omega
        · have : E - 1 = n + T - 2 ^ 62 - f.p := by rw [hEdef, if_neg hc]; omega
          omega
      obtain ⟨_, a1, a2, a3⟩ := qOf_drop u e tb sticky φ h0 h1 hs hu (by rw [hE]; omega)
        (by rw [hE]; exact hE1) (by rw [hE]; exact hd) r (by rw [hE]) hr0 Q rfl
      have hsplit : (2 : ℝ) ^ (E - 1) = 2 ^ r * (2 : ℝ) ^ t := two_zpow_split (E - 1) r t (by omega)
      refine ⟨hE1, hupper, hlower, ?_, ?_, ?_⟩
      · rw [hsplit]
        calc 2 * y = (2 * ((u.toNat : ℝ) + φ)) * 2 ^ t := by rw [hydef]; ring
          _ ≤ ((2 * Q + 1) * 2 ^ r) * 2 ^ t := mul_le_mul_of_nonneg_right a1 ht2.le
          _ = _ := by ring
      · rw [hsplit]
        calc 2 * (Q : ℝ) * (2 ^ r * 2 ^ t) = (2 * Q * 2 ^ r) * 2 ^ t := by ring
          _ ≤ (2 * ((u.toNat : ℝ) + φ) + 2 ^ r) * 2 ^ t := mul_le_mul_of_nonneg_right a2 ht2.le
          _ = _ := by rw [hydef]; ring
      · intro ht
        apply a3
        rw [hsplit] at ht
        rcases ht with ht | ht
        · left
          apply mul_right_cancel₀ ht2.ne'
          calc 2 * ((u.toNat : ℝ) + φ) * 2 ^ t = 2 * y := by rw [hydef]; ring
            _ = _ := ht
            _ = _ := by ring
        · right
          apply mul_right_cancel₀ ht2.ne'
          calc (2 * ((u.toNat : ℝ) + φ) + 2 ^ r) * 2 ^ t = 2 * y + 2 ^ r * 2 ^ t := by
                rw [hydef]; ring
            _ = _ := ht
            _ = _ := by ring
    · -- the significand is shifted left, exactly
      push Not at hd
      have hst : sticky = false := by
        cases hsc : sticky
        · rfl
        · have := hsb hsc
          exfalso
          by_cases hc : n + T ≤ f.p + 2 ^ 62
          · have : E = 1 := by rw [hEdef, if_pos hc]
            omega
          · have : E - 1 = n + T - 2 ^ 62 - f.p := by rw [hEdef, if_neg hc]; omega
            omega
      have hφ : φ = 0 := by
        rw [hst] at hs; have := of_decide_eq_false hs.symm; linarith
      set k := T - 2 ^ 62 - (E - 1) with hkdef
      have hsplit : (2 : ℝ) ^ t = 2 ^ k * 2 ^ (E - 1) := by
        rw [← pow_add, ← zpow_natCast]; congr 1; omega
      have hyQ : y = ((u.toNat * 2 ^ k : ℕ) : ℝ) * 2 ^ (E - 1) := by
        rw [hydef, hφ, hsplit]; push_cast; ring
      have hbound : u.toNat * 2 ^ k < 2 ^ f.p := by
        have h2 : (0 : ℝ) < 2 ^ (E - 1) := by positivity
        have := hupper
        rw [hyQ] at this
        have := lt_of_mul_lt_mul_right this h2.le
        exact_mod_cast this
      have hk60 : k < 60 := by
        have : 2 ^ k ≤ u.toNat * 2 ^ k := Nat.le_mul_of_pos_left _ (by omega)
        have : 2 ^ k < 2 ^ 60 :=
          lt_of_lt_of_le (lt_of_le_of_lt this hbound) (Nat.pow_le_pow_right (by norm_num) hp60)
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
      have htb : (tb - 0x4000000000000000).toNat = T - 2 ^ 62 := by
        rw [toNat_sub' _ _ (by rw [bias_toNat]; omega), bias_toNat]
      have hkw : (tb - 0x4000000000000000 - (e - 1)).toNat = k := by
        rw [toNat_sub' _ _ (by rw [htb, he1w]; omega), htb, he1w]
      have hQv : Q = u.toNat * 2 ^ k := by
        rw [hQdef]
        unfold qOf
        have hsum' : (e - 1 + 0x4000000000000000).toNat = E - 1 + 2 ^ 62 := by
          rw [toNat_add' _ _ (by rw [he1w, bias_toNat]; omega), he1w, bias_toNat]
        rw [if_neg (fun h => by
          have h' := UInt64.le_iff_toNat_le.mp h
          rw [hsum'] at h'
          omega)]
        rw [shl_word _ _ (by rw [hkw]; omega) (by rw [hkw]; calc u.toNat * 2 ^ k < 2 ^ f.p := hbound
            _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)), hkw]
      have hyQ' : y = (Q : ℝ) * 2 ^ (E - 1) := by rw [hyQ, hQv]
      have hS : (0 : ℝ) < 2 ^ (E - 1) := by positivity
      refine ⟨hE1, hupper, hlower, ?_, ?_, fun ht => ?_⟩
      · rw [hyQ']; linarith only [hS]
      · rw [hyQ']; linarith only [hS]
      · exfalso
        rw [hyQ'] at ht
        rcases ht with ht | ht
        · linarith only [ht, hS]
        · linarith only [ht, hS]
  rw [positive_reference f y E Q hR]
  obtain ⟨hQ2, _⟩ := significand_bounds f y E Q hR
  have hhalf : half f = 2 ^ (f.p - 1) := rfl
  have hEb : (E - 1) * 2 ^ (f.p - 1) < 2 ^ 62 :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hlim
  have hQb : Q ≤ 2 ^ 61 := by
    rw [hhalf] at hQ2
    have : 2 ^ (f.p - 1) ≤ 2 ^ 59 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hprod : ((e - 1) * ((1 : UInt64) <<< (p - 1))).toNat = (E - 1) * 2 ^ (f.p - 1) := by
    rw [toNat_mul' _ _ (by rw [he1w, hpw]; omega), he1w, hpw]
  have hsum : ((e - 1) * ((1 : UInt64) <<< (p - 1)) + qOf u sticky tb e).toNat =
      pack f E Q := by
    unfold pack
    rw [toNat_add' _ _ (by rw [hprod, ← hQdef]; omega), hprod, ← hQdef, hhalf]
  unfold packInf
  have hnF : ¬ (f.F ≤ E) := by omega
  simp only [hnF, false_or]
  by_cases hc : limit f ≤ pack f E Q
  · rw [if_pos (UInt64.le_iff_toNat_le.mpr (by rw [hsum, hFs]; exact hc)), if_pos hc, hFs]
  · rw [if_neg (fun h => hc (by have := UInt64.le_iff_toNat_le.mp h; rwa [hsum, hFs] at this)),
      if_neg hc, hsum]

#print axioms round_shift
#print axioms qOf_drop
#print axioms roundUnits_spec

end Verified.Examples.ParseFloatRound
