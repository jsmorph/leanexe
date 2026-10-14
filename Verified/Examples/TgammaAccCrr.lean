import Verified.Examples.TgammaDD
import Verified.Examples.TgammaWords
import Verified.Examples.TgammaMainRed

/-!
The correction term of `Tgamma.accurate`.  CORE-MATH adds `fh jm crr` (for `jm ≤ 0`) or subtracts
`1.04 fh (jm - 5) crr` (for `jm > 0`) to the low part, where `crr` combines sums of the constants
`2 ^ -53`, `2 ^ -54`, and `2 ^ -107` that cancel in round-to-nearest; the term corrects directed
roundings.  For one step its value is not needed: `crr` is at most `2 ^ -104` in magnitude whatever
the rounding of the four operations (`crr_le`, `crr2_le`), so the adjusted low part moves by at most
`2 ^ -95 |fh|` and a rounding of the low part (`adj_low`).
-/

namespace Verified.Examples.TgammaAccCrr
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaDD

set_option exponentiation.threshold 4096

/-- The adjusted low part of `Tgamma.accurate`. -/
def adjLow (fh fl jm : Float) : Float :=
  if jm ≤ 0.0 then
    fl + fh * (jm * (((Float.ofBits 0x3C90000000000000 + Float.ofBits 0x3940000000000000) -
      Float.ofBits 0x3C90000000000000) + ((Float.ofBits 0x3CA0000000000000 -
      Float.ofBits 0x3940000000000000) - Float.ofBits 0x3CA0000000000000)))
  else
    fl - fh * ((jm - 5.0) *
      (if Float.ofBits 0x3CA0000000000000 - Float.ofBits 0x3940000000000000 ==
          -(-Float.ofBits 0x3CA0000000000000 + Float.ofBits 0x3940000000000000) then
        Float.ofBits 0x3CA0000000000000 - (Float.ofBits 0x3CA0000000000000 -
          Float.ofBits 0x3940000000000000)
       else 0.0) * Float.ofBits 0x3FF0A3D70A3D70A4)

theorem fa_lit (w : UInt64) (q : ℚ) (hw : Wasm.IEEE64.isFinite w = true)
    (hq : PolyBound.ratOfWord w = q) : FApprox (Float.ofBits w) (q : ℝ) 0 := by
  have h := fapprox_self _ (TgammaWords.ofBits_finite _ hw)
  rwa [TgammaWords.ofBits_value _ hw, hq] at h

/-- **`crr` for `jm ≤ 0`** is at most `2 ^ -104`. -/
theorem crr_le :
    Finite (((Float.ofBits 0x3C90000000000000 + Float.ofBits 0x3940000000000000) -
      Float.ofBits 0x3C90000000000000) + ((Float.ofBits 0x3CA0000000000000 -
      Float.ofBits 0x3940000000000000) - Float.ofBits 0x3CA0000000000000)).toBits ∧
    |value (((Float.ofBits 0x3C90000000000000 + Float.ofBits 0x3940000000000000) -
      Float.ofBits 0x3C90000000000000) + ((Float.ofBits 0x3CA0000000000000 -
      Float.ofBits 0x3940000000000000) - Float.ofBits 0x3CA0000000000000)).toBits| ≤
      1 / 2 ^ 104 := by
  have h54 := fa_lit 0x3C90000000000000 (1 / 2 ^ 54) (by decide) (by decide +kernel)
  have h53 := fa_lit 0x3CA0000000000000 (1 / 2 ^ 53) (by decide) (by decide +kernel)
  have h107 := fa_lit 0x3940000000000000 (1 / 2 ^ 107) (by decide) (by decide +kernel)
  push_cast at h54 h53 h107
  have a1 := fapprox_add h54 h107 (1 / 2 ^ 53) (by norm_num) (by norm_num)
  have a2 := fapprox_sub a1 h54 (1 / 2 ^ 105) (by norm_num) (by norm_num)
  have b1 := fapprox_sub h53 h107 (1 / 2 ^ 52) (by norm_num) (by norm_num)
  have b2 := fapprox_sub b1 h53 (1 / 2 ^ 104) (by norm_num) (by norm_num)
  have c := fapprox_add a2 b2 (1 / 2 ^ 104) (by norm_num) (by norm_num)
  refine ⟨c.1, ?_⟩
  have := Approx.mag c
  norm_num at this ⊢
  linarith

/-- **`crr` for `jm > 0`** is at most `2 ^ -104`. -/
theorem crr2_le :
    Finite (if Float.ofBits 0x3CA0000000000000 - Float.ofBits 0x3940000000000000 ==
          -(-Float.ofBits 0x3CA0000000000000 + Float.ofBits 0x3940000000000000) then
        Float.ofBits 0x3CA0000000000000 - (Float.ofBits 0x3CA0000000000000 -
          Float.ofBits 0x3940000000000000)
       else 0.0).toBits ∧
    |value (if Float.ofBits 0x3CA0000000000000 - Float.ofBits 0x3940000000000000 ==
          -(-Float.ofBits 0x3CA0000000000000 + Float.ofBits 0x3940000000000000) then
        Float.ofBits 0x3CA0000000000000 - (Float.ofBits 0x3CA0000000000000 -
          Float.ofBits 0x3940000000000000)
       else 0.0).toBits| ≤ 1 / 2 ^ 104 := by
  have h53 := fa_lit 0x3CA0000000000000 (1 / 2 ^ 53) (by decide) (by decide +kernel)
  have h107 := fa_lit 0x3940000000000000 (1 / 2 ^ 107) (by decide) (by decide +kernel)
  push_cast at h53 h107
  have b1 := fapprox_sub h53 h107 (1 / 2 ^ 52) (by norm_num) (by norm_num)
  have b2 := fapprox_sub h53 b1 (1 / 2 ^ 104) (by norm_num) (by norm_num)
  split_ifs
  · refine ⟨b2.1, ?_⟩
    have := Approx.mag b2
    norm_num at this ⊢
    linarith
  · refine ⟨TgammaMainRed.zero_finite, ?_⟩
    rw [TgammaMainRed.zero_value]; norm_num

/-- A rounded product with bounds `A` and `B` on its factors. -/
theorem mul_bound (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (A B : ℝ)
    (hA : |value a.toBits| ≤ A) (hB : |value b.toBits| ≤ B) (hAB : A * B ≤ 2 ^ 1000) :
    Finite (a * b).toBits ∧ |value (a * b).toBits| ≤ 2 * (A * B) + 1 / 2 ^ 1075 := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have h := fapprox_mul (fapprox_self a ha) (fapprox_self b hb) A B hA hB ((A + 0) * (B + 0))
    le_rfl (by simp only [add_zero]; linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1022)])
  simp only [zero_mul, mul_zero, add_zero, zero_add] at h
  refine ⟨h.1, ?_⟩
  have h1 := Approx.mag h
  rw [abs_mul] at h1
  have h2 : |value a.toBits| * |value b.toBits| ≤ A * B := mul_le_mul hA hB (abs_nonneg _) hA0
  have h3 : A * B / 2 ^ 53 ≤ A * B := div_le_self (by positivity) (by norm_num)
  linarith

/-- The sum or difference of `fl` with a term `t` at most `2 ^ -90 |fh|`. -/
theorem add_small (fh fl t : Float) (hfl : Finite fl.toBits) (ht : Finite t.toBits)
    (hfh2 : |value fh.toBits| ≤ 2 ^ 900) (hflb : |value fl.toBits| ≤ |value fh.toBits| / 2 ^ 30)
    (htb : |value t.toBits| ≤ |value fh.toBits| / 2 ^ 90) :
    (Finite (fl + t).toBits ∧ |value (fl + t).toBits - value fl.toBits| ≤
        |value fh.toBits| / 2 ^ 81) ∧
      (Finite (fl - t).toBits ∧ |value (fl - t).toBits - value fl.toBits| ≤
        |value fh.toBits| / 2 ^ 81) := by
  set F := |value fh.toBits|
  have hF0 : 0 ≤ F := abs_nonneg _
  have hB : |value fl.toBits| + |value t.toBits| ≤ F / 2 ^ 29 := by
    have : F / 2 ^ 90 ≤ F / 2 ^ 30 := div_le_div_of_nonneg_left hF0 (by positivity) (by norm_num)
    linarith [(by ring : F / 2 ^ 29 = F / 2 ^ 30 + F / 2 ^ 30)]
  have hBm : F / 2 ^ 29 < 2 ^ 1023 := by
    have : F / 2 ^ 29 ≤ F := div_le_self hF0 (by norm_num)
    linarith [(by norm_num : (2 : ℝ) ^ 900 < 2 ^ 1023)]
  have ha := fapprox_add (fapprox_self fl hfl) (fapprox_self t ht) _
    (by simp only [add_zero]; exact (abs_add_le _ _).trans hB) hBm
  have hs := fapprox_sub (fapprox_self fl hfl) (fapprox_self t ht) _
    (by simp only [add_zero]; exact (abs_sub _ _).trans hB) hBm
  simp only [zero_add] at ha hs
  have e1 : F / 2 ^ 29 / 2 ^ 53 + F / 2 ^ 90 ≤ F / 2 ^ 81 := by
    have e2 : F / 2 ^ 29 / 2 ^ 53 + F / 2 ^ 90 = F * (1 / 2 ^ 82 + 1 / 2 ^ 90) := by ring
    have e3 : F / 2 ^ 81 = F * (1 / 2 ^ 81) := by ring
    rw [e2, e3]
    exact mul_le_mul_of_nonneg_left (by norm_num) hF0
  refine ⟨⟨ha.1, ?_⟩, ⟨hs.1, ?_⟩⟩
  · have h4 := abs_sub_le (value (fl + t).toBits) (value fl.toBits + value t.toBits)
      (value fl.toBits)
    rw [show value fl.toBits + value t.toBits - value fl.toBits = value t.toBits by ring] at h4
    linarith [ha.2]
  · have h4 := abs_sub_le (value (fl - t).toBits) (value fl.toBits - value t.toBits)
      (value fl.toBits)
    rw [show value fl.toBits - value t.toBits - value fl.toBits = -value t.toBits by ring,
      abs_neg] at h4
    linarith [hs.2]

/-- **The adjusted low part** moves by at most `2 ^ -81 |fh|`. -/
theorem adj_low (fh fl jm : Float) (hfh : Finite fh.toBits) (hfl : Finite fl.toBits)
    (hjm : Finite jm.toBits) (hjmb : |value jm.toBits| ≤ 200)
    (hfh1 : 1 / 2 ^ 900 ≤ |value fh.toBits|) (hfh2 : |value fh.toBits| ≤ 2 ^ 900)
    (hflb : |value fl.toBits| ≤ |value fh.toBits| / 2 ^ 30) :
    Finite (adjLow fh fl jm).toBits ∧
      |value (adjLow fh fl jm).toBits - value fl.toBits| ≤ |value fh.toBits| / 2 ^ 81 := by
  set F := |value fh.toBits| with hFdef
  have htiny : (1 : ℝ) / 2 ^ 1075 ≤ F / 2 ^ 170 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 * 2 ^ 170 ≤ 1 / 2 ^ 900)]
  -- `t = fh m` for `|m| ≤ 2 ^ -92`
  have ht : ∀ m : Float, Finite m.toBits → |value m.toBits| ≤ 1 / 2 ^ 92 →
      Finite (fh * m).toBits ∧ |value (fh * m).toBits| ≤ F / 2 ^ 90 := by
    intro m hmf hmb
    obtain ⟨hpf, hpb⟩ := mul_bound fh m hfh hmf F (1 / 2 ^ 92) le_rfl hmb
      (by nlinarith [(by norm_num : (2 : ℝ) ^ 900 * (1 / 2 ^ 92) ≤ 2 ^ 1000)])
    refine ⟨hpf, ?_⟩
    have e1 : 2 * (F * (1 / 2 ^ 92)) + F / 2 ^ 170 ≤ F / 2 ^ 90 := by
      have e2 : 2 * (F * (1 / 2 ^ 92)) + F / 2 ^ 170 = F * (2 / 2 ^ 92 + 1 / 2 ^ 170) := by ring
      have e3 : F / 2 ^ 90 = F * (1 / 2 ^ 90) := by ring
      rw [e2, e3]
      exact mul_le_mul_of_nonneg_left (by norm_num) (abs_nonneg _)
    linarith
  unfold adjLow
  by_cases hj : jm ≤ 0.0
  · rw [ite_eq_left hj]
    obtain ⟨hcf, hcb⟩ := crr_le
    obtain ⟨hmf, hmb⟩ := mul_bound jm _ hjm hcf 200 (1 / 2 ^ 104) hjmb hcb (by norm_num)
    obtain ⟨htf, htb⟩ := ht _ hmf (by linarith [(by norm_num : (2 : ℝ) * (200 * (1 / 2 ^ 104)) +
      1 / 2 ^ 1075 ≤ 1 / 2 ^ 92)])
    exact (add_small fh fl _ hfl htf hfh2 hflb htb).1
  · rw [ite_eq_right hj]
    obtain ⟨hcf, hcb⟩ := crr2_le
    have h5f : Finite (5.0 : Float).toBits := by
      rw [show (5.0 : Float).toBits = 0x4014000000000000 from rfl]
      unfold CodeLib.IEEE64.Finite; decide
    have h5v : value (5.0 : Float).toBits = 5 := by
      rw [show (5.0 : Float).toBits = 0x4014000000000000 from rfl,
        TgammaSpecial.lit_value 0x4014000000000000 5 (by decide +kernel)]
      norm_num
    have hs5 := fapprox_sub (fapprox_self jm hjm) (fapprox_self _ h5f) 206 (by
      rw [h5v, add_zero]
      have := abs_sub (value jm.toBits) 5
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 5)] at this
      linarith) (by norm_num)
    have hm0b : |value (jm - 5.0).toBits| ≤ 207 := by
      have := Approx.mag hs5
      have h6 := abs_sub (value jm.toBits) (value (5.0 : Float).toBits)
      rw [h5v, abs_of_pos (by norm_num : (0 : ℝ) < 5)] at h6
      rw [h5v] at this
      linarith
    obtain ⟨hm1f, hm1b⟩ := mul_bound _ _ hs5.1 hcf 207 (1 / 2 ^ 104) hm0b hcb (by norm_num)
    have hcw : Wasm.IEEE64.isFinite 0x3FF0A3D70A3D70A4 = true := by decide
    have hcq : PolyBound.ratOfWord 0x3FF0A3D70A3D70A4 ≤ 2 ∧
        0 ≤ PolyBound.ratOfWord 0x3FF0A3D70A3D70A4 := by decide +kernel
    have hcb2 : |value (Float.ofBits 0x3FF0A3D70A3D70A4).toBits| ≤ 2 := by
      rw [TgammaWords.ofBits_value _ hcw, abs_of_nonneg (by exact_mod_cast hcq.2)]
      exact_mod_cast hcq.1
    obtain ⟨hm2f, hm2b⟩ := mul_bound _ _ hm1f (TgammaWords.ofBits_finite _ hcw)
      (2 * (207 * (1 / 2 ^ 104)) + 1 / 2 ^ 1075) 2 hm1b hcb2 (by norm_num)
    obtain ⟨htf, htb⟩ := ht _ hm2f (by linarith [(by norm_num : (2 : ℝ) * ((2 * (207 *
      (1 / 2 ^ 104)) + 1 / 2 ^ 1075) * 2) + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 92)])
    exact (add_small fh fl _ hfl htf hfh2 hflb htb).2

#print axioms mul_bound
#print axioms add_small
#print axioms adj_low

#print axioms crr_le
#print axioms crr2_le

end Verified.Examples.TgammaAccCrr
