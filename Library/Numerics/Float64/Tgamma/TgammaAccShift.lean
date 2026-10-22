import Library.Numerics.Float64.Tgamma.TgammaMulDD3
import Library.Numerics.Float64.Tgamma.TgammaAcc1
import Library.Numerics.Float64.Tgamma.TgammaMainLoop

/-!
The factors of the shift loops in the accurate path of `Tgamma`.  The loop for `x < j` keeps
`x + k` as a double-double `xph + xpl` and moves to `x + k + 1` with `shiftHi`, an addition of the
low parts, and `fastTwoSum` (`fshift`).  Every value involved is a multiple of `2 ^ -54`, since
`|x| ≥ 1/4`, and the low parts stay below `2 ^ -43`, so each step is exact: the factor
`xph + xpl` equals `x + k` at every step (`fshift_spec`).  The case where `fastTwoSum` lacks
Dekker's ordering is exact because the sum is then below `2 ^ -41` and representable.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccShift
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAcc1 TgammaMainLoop

set_option exponentiation.threshold 4096

/-- A double of magnitude at least `2 ^ -b` is a multiple of `2 ^ -(52 + b)`. -/
theorem grid_neg (w : UInt64) (b : ℕ) (hb : b ≤ 1000) (h : 1 / (2 : ℝ) ^ b ≤ |value w|) :
    ∃ k : ℤ, value w = k / 2 ^ (52 + b) := by
  have he : 1023 - b ≤ Wasm.IEEE64.exponent w := by
    by_contra hc
    have := F64Magnitude.magnitude_lt w (1023 - b) (-(b : ℤ)) (by omega) (by omega) (by omega)
    rw [zpow_neg, zpow_natCast] at this
    rw [one_div] at h
    linarith
  obtain ⟨k, hk⟩ := F64Sterbenz.scaled_dvd w (1022 - b) (by omega)
  refine ⟨k, ?_⟩
  rw [value, hk]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity),
    show (2 : ℝ) ^ 1074 = 2 ^ (1022 - b) * 2 ^ (52 + b) by rw [← pow_add]; congr 1; omega]
  ring

/-- One step of the factor `xph + xpl` from `x + k` to `x + k + 1`. -/
def fshift (xph xpl : Float) : Float × Float :=
  fastTwoSum (shiftHi xph).1 (xpl + (shiftHi xph).2)

/-- A number on the grid `2 ^ -54` with magnitude at most `2 ^ -1` is the value of the sum of two
doubles whose values add to it. -/
theorem small_num (v : ℝ) (z : ℤ) (hz : v = z / 2 ^ 54) (hv : |v| ≤ 1 / 2) :
    |(z : ℝ)| ≤ 2 ^ 53 := by
  have : (z : ℝ) = v * 2 ^ 54 := by rw [hz]; field_simp
  rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 54)]
  have := mul_le_mul_of_nonneg_right hv (by positivity : (0 : ℝ) ≤ 2 ^ 54)
  linarith [(by norm_num : (1 : ℝ) / 2 * 2 ^ 54 = 2 ^ 53)]

theorem int_abs_le (z : ℤ) (h : |(z : ℝ)| ≤ 2 ^ 53) : |z| ≤ 2 ^ 53 := by
  rw [← Int.cast_abs] at h
  exact_mod_cast h

/-- **One exact step of the factor.** -/
theorem fshift_spec (xph xpl : Float) (hph : Finite xph.toBits) (hpl : Finite xpl.toBits)
    (zh zl : ℤ) (hzh : value xph.toBits = zh / 2 ^ 54) (hzl : value xpl.toBits = zl / 2 ^ 54)
    (hpl43 : |value xpl.toBits| ≤ 1 / 2 ^ 43)
    (hX : |value xph.toBits + value xpl.toBits + 1| ≤ 2 ^ 8)
    (hX0 : |value xph.toBits + value xpl.toBits| ≤ 2 ^ 8) :
    Finite (fshift xph xpl).1.toBits ∧ Finite (fshift xph xpl).2.toBits ∧
      value (fshift xph xpl).1.toBits + value (fshift xph xpl).2.toBits =
        value xph.toBits + value xpl.toBits + 1 ∧
      (∃ z : ℤ, value (fshift xph xpl).1.toBits = z / 2 ^ 54) ∧
      (∃ z : ℤ, value (fshift xph xpl).2.toBits = z / 2 ^ 54) ∧
      |value (fshift xph xpl).2.toBits| ≤ 1 / 2 ^ 43 ∧
      |value (fshift xph xpl).2.toBits| ≤ |value (fshift xph xpl).1.toBits| / 2 ^ 52 +
        1 / 2 ^ 1074 := by
  have hxph : |value xph.toBits| ≤ 2 ^ 8 + 1 := by
    have := abs_add_le (value xph.toBits + value xpl.toBits) (-value xpl.toBits)
    rw [show value xph.toBits + value xpl.toBits + -value xpl.toBits = value xph.toBits by ring,
      abs_neg] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 ≤ 1)]
  obtain ⟨ha1f, ha2f, hasum, ha2b⟩ := shiftHi_spec xph hph
    (by linarith [(by norm_num : (2 : ℝ) ^ 8 + 1 < 2 ^ 899)])
  unfold fshift
  set A := shiftHi xph with hAdef
  -- bounds on `A`
  have hA1 : |value A.1.toBits| ≤ 2 ^ 8 + 2 := by
    have h1 := abs_add_le (value A.1.toBits + value A.2.toBits) (-value A.2.toBits)
    rw [show value A.1.toBits + value A.2.toBits + -value A.2.toBits = value A.1.toBits by ring,
      abs_neg] at h1
    have h2 : |value xph.toBits + 1| ≤ 2 ^ 8 + 1 / 2 ^ 43 := by
      have := abs_add_le (value xph.toBits + value xpl.toBits + 1) (-value xpl.toBits)
      rw [show value xph.toBits + value xpl.toBits + 1 + -value xpl.toBits = value xph.toBits + 1
        by ring, abs_neg] at this
      linarith
    rw [hasum] at h1
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 + 1 / 2 ^ 1074 ≤ 1)]
  have hA2 : |value A.2.toBits| ≤ 1 / 2 ^ 43 := by
    have : |value A.1.toBits| / 2 ^ 52 ≤ (2 ^ 8 + 2) / 2 ^ 52 :=
      div_le_div_of_nonneg_right hA1 (by norm_num)
    linarith [(by norm_num : ((2 : ℝ) ^ 8 + 2) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 43)]
  -- `A` on the grid `2 ^ -54`
  have hgA : (∃ z : ℤ, value A.1.toBits = z / 2 ^ 54) ∧ ∃ z : ℤ, value A.2.toBits = z / 2 ^ 54 := by
    by_cases hbig : 1 / (2 : ℝ) ^ 2 ≤ |value A.1.toBits|
    · obtain ⟨z1, hz1⟩ := grid_neg A.1.toBits 2 (by norm_num) hbig
      refine ⟨⟨z1, hz1⟩, ⟨zh + 2 ^ 54 - z1, ?_⟩⟩
      have : value A.2.toBits = value xph.toBits + 1 - value A.1.toBits := by linarith
      rw [this, hzh, hz1]
      push_cast
      field_simp
      ring
    · push Not at hbig
      have hs : |value xph.toBits + 1| ≤ 1 / 2 := by
        rw [← hasum]
        have := abs_add_le (value A.1.toBits) (value A.2.toBits)
        have : |value A.1.toBits| / 2 ^ 52 ≤ 1 / 2 ^ 2 / 2 ^ 52 :=
          div_le_div_of_nonneg_right hbig.le (by norm_num)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 2 + 1 / 2 ^ 2 / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2)]
      have hv : value xph.toBits + 1 = ((zh + 2 ^ 54 : ℤ) : ℝ) / 2 ^ 54 := by
        rw [hzh]; push_cast; ring
      have hex := shiftHi_exact xph hph (zh + 2 ^ 54) 1020 (by norm_num)
        (by rw [hv, div_mul_eq_mul_div, mul_div_assoc,
          show (2 : ℝ) ^ 1074 / 2 ^ 54 = 2 ^ 1020 by norm_num])
        (small_num _ _ hv hs)
      have hex' : value A.1.toBits = value xph.toBits + 1 := hex
      refine ⟨⟨zh + 2 ^ 54, by rw [hex', hv]⟩, ⟨0, ?_⟩⟩
      have : value A.2.toBits = 0 := by linarith
      rw [this]; simp
  obtain ⟨⟨z1, hz1⟩, ⟨z2, hz2⟩⟩ := hgA
  -- `t = xpl + A.2`, exact
  have htv : value xpl.toBits + value A.2.toBits = ((zl + z2 : ℤ) : ℝ) / 2 ^ 54 := by
    rw [hzl, hz2]; push_cast; ring
  obtain ⟨htf, htv'⟩ := grid_add xpl A.2 hpl ha2f (zl + z2) 54 htv
    (int_abs_le _ (small_num _ _ htv (by
      have := abs_add_le (value xpl.toBits) (value A.2.toBits)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 + 1 / 2 ^ 43 ≤ 1 / 2)]))) (by norm_num)
  generalize xpl + A.2 = t at htf htv' ⊢
  have htz : value t.toBits = ((zl + z2 : ℤ) : ℝ) / 2 ^ 54 := by rw [htv', htv]
  have htb : |value t.toBits| ≤ 1 / 2 ^ 42 := by
    rw [htv']
    have := abs_add_le (value xpl.toBits) (value A.2.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 43 + 1 / 2 ^ 43 = 1 / 2 ^ 42)]
  have hsumX : value A.1.toBits + value t.toBits = value xph.toBits + value xpl.toBits + 1 := by
    rw [htv']; linarith
  have hXz : value A.1.toBits + value t.toBits = ((z1 + (zl + z2) : ℤ) : ℝ) / 2 ^ 54 := by
    rw [hz1, htz]; push_cast; ring
  by_cases hsmall : |value A.1.toBits + value t.toBits| ≤ 1 / 2
  · -- a small sum is exact, and so is every step of `fastTwoSum`
    have hz : |z1 + (zl + z2)| ≤ 2 ^ 53 := int_abs_le _ (small_num _ _ hXz hsmall)
    obtain ⟨hsf, hsv⟩ := grid_add A.1 t ha1f htf _ 54 hXz hz (by norm_num)
    have hdz : value (A.1 + t).toBits - value A.1.toBits = ((zl + z2 : ℤ) : ℝ) / 2 ^ 54 := by
      rw [hsv, htz]; ring
    obtain ⟨hdf, hdv⟩ := grid_sub (A.1 + t) A.1 hsf ha1f (zl + z2) 54 hdz
      (int_abs_le _ (small_num _ _ htz (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 42 ≤ 1 / 2)])))
      (by norm_num)
    have hez : value t.toBits - value ((A.1 + t) - A.1).toBits = ((0 : ℤ) : ℝ) / 2 ^ 54 := by
      rw [hdv, hsv]; push_cast; ring
    obtain ⟨hef, hev⟩ := grid_sub t ((A.1 + t) - A.1) htf hdf 0 54 hez (by norm_num) (by norm_num)
    have hfts : fastTwoSum A.1 t = (A.1 + t, t - ((A.1 + t) - A.1)) := rfl
    rw [hfts]
    have he0 : value (t - ((A.1 + t) - A.1)).toBits = 0 := by rw [hev, hdv, hsv]; ring
    refine ⟨hsf, hef, by rw [he0, hsv, hsumX, add_zero], ⟨_, by rw [hsv, hXz]⟩,
      ⟨0, by rw [he0]; simp⟩, by rw [he0, abs_zero]; positivity,
      by rw [he0, abs_zero]; positivity⟩
  · -- a larger sum has Dekker's ordering
    push Not at hsmall
    have hord : |value t.toBits| ≤ |value A.1.toBits| := by
      have := abs_sub_abs_le_abs_sub (value A.1.toBits + value t.toBits) (value t.toBits)
      rw [add_sub_cancel_right] at this
      linarith [(by norm_num : (1 : ℝ) / 2 - 1 / 2 ^ 42 ≥ 1 / 2 ^ 42)]
    obtain ⟨hsf, hef, hsum2, -, heb⟩ := fastTwoSum_spec A.1 t ha1f htf hord
      (by linarith [(by norm_num : (2 : ℝ) ^ 8 + 2 < 2 ^ 900)])
    generalize fastTwoSum A.1 t = S at hsf hef hsum2 heb ⊢
    have hS1 : |value S.1.toBits| ≤ 2 ^ 8 + 1 := by
      have h1 := abs_add_le (value S.1.toBits + value S.2.toBits) (-value S.2.toBits)
      rw [show value S.1.toBits + value S.2.toBits + -value S.2.toBits = value S.1.toBits by ring,
        abs_neg, hsum2, hsumX] at h1
      have h0 := abs_nonneg (value S.1.toBits)
      have : |value S.1.toBits| / 2 ^ 52 ≤ |value S.1.toBits| / 2 :=
        div_le_div_of_nonneg_left h0 (by norm_num) (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1074 ≤ 1 / 2)]
    have hS2 : |value S.2.toBits| ≤ 1 / 2 ^ 43 := by
      have : |value S.1.toBits| / 2 ^ 52 ≤ (2 ^ 8 + 1) / 2 ^ 52 :=
        div_le_div_of_nonneg_right hS1 (by norm_num)
      linarith [(by norm_num : ((2 : ℝ) ^ 8 + 1) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 43)]
    have hbig : 1 / (2 : ℝ) ^ 2 ≤ |value S.1.toBits| := by
      have := abs_sub_abs_le_abs_sub (value S.1.toBits + value S.2.toBits) (value S.2.toBits)
      rw [add_sub_cancel_right, hsum2] at this
      linarith [(by norm_num : (1 : ℝ) / 2 - 1 / 2 ^ 43 ≥ 1 / 2 ^ 2)]
    obtain ⟨z3, hz3⟩ := grid_neg S.1.toBits 2 (by norm_num) hbig
    refine ⟨hsf, hef, by rw [hsum2, hsumX], ⟨z3, hz3⟩, ⟨z1 + (zl + z2) - z3, ?_⟩, hS2, heb⟩
    have : value S.2.toBits = value A.1.toBits + value t.toBits - value S.1.toBits := by linarith
    rw [this, hXz, hz3]; push_cast; ring

#print axioms grid_neg
#print axioms fshift_spec

end Library.Numerics.Float64.Tgamma.TgammaAccShift
