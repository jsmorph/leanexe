import Verified.Examples.TgammaRecipDD
import Verified.Examples.TgammaMul
import Verified.Examples.TgammaMainRed
import Verified.Examples.TgammaTiny
import Verified.Examples.TgammaApprox

/-!
The first product of `Tgamma.asLgammaAsym`: `(x - 1/2)(log xh - 1 + l + dz)` with `x = xh + xl`,
for `4 ≤ xh ≤ 186`.  `asLogd` enters through `LogdSpec`, the statement that track `expm1` proves:
its low part is not renormalized and reaches `2 ^ -22`.  The subtractions `xh - 1/2` and `lh - 1`
are exact, since the subtrahend is a multiple of the spacing of the binade of the minuend
(`sub_exact_binade`).  The product then lies within `2 ^ -63` of its exact value, and its low part
stays below `0.73 · 2 ^ -14` (`asym_prod`).
-/

namespace Verified.Examples.TgammaAsym1
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaMainRed TgammaRecip
  TgammaFloor

set_option exponentiation.threshold 4096

/-- The specification of `Tgamma.asLogd` on `[4, 186]` in the form that track `expm1` states. -/
def LogdSpec : Prop :=
  ∀ x : Float, Finite x.toBits → 4 ≤ value x.toBits → value x.toBits ≤ 186 →
    Finite (asLogd logdTable x).1.toBits ∧ Finite (asLogd logdTable x).2.toBits ∧
    |value (asLogd logdTable x).1.toBits + value (asLogd logdTable x).2.toBits -
        Real.log (value x.toBits)| ≤ 1 / 2 ^ 69 + |Real.log (value x.toBits)| / 2 ^ 78 ∧
    |value (asLogd logdTable x).2.toBits| ≤
      1 / 2 ^ 22 + |value (asLogd logdTable x).1.toBits| / 2 ^ 52

/-- A difference `a - b` with `0 ≤ b ≤ a`, `a` in the binade `[2 ^ e, 2 ^ (e + 1))`, and `b` a
multiple of the spacing `2 ^ (e - 52)` of that binade is exact. -/
theorem sub_exact_binade (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (e : ℕ)
    (he : e ≤ 1000) (hlo : (2 : ℝ) ^ e ≤ value a.toBits) (hhi : value a.toBits < 2 ^ (e + 1))
    (hb0 : 0 ≤ value b.toBits) (hba : value b.toBits ≤ value a.toBits) (m : ℤ)
    (hbm : value b.toBits * 2 ^ 1074 = m * 2 ^ (1022 + e)) :
    Finite (a - b).toBits ∧ value (a - b).toBits = value a.toBits - value b.toBits := by
  have hpos : (0 : ℝ) < 2 ^ e := by positivity
  obtain ⟨K, hK⟩ := grid a.toBits ha (1021 + e) (by omega) (by
    rw [abs_of_pos (by linarith)]
    rw [show (2 : ℝ) ^ (53 + (1021 + e)) / 2 ^ 1074 = 2 ^ e by
      rw [show 53 + (1021 + e) = 1074 + e by omega, pow_add]; field_simp]
    exact hlo)
  rw [show 1021 + e + 1 = 1022 + e by omega] at hK
  have hP : (0 : ℝ) < 2 ^ (1022 + e) := by positivity
  have h1 : ((K - m : ℤ) : ℝ) * 2 ^ (1022 + e) = (value a.toBits - value b.toBits) * 2 ^ 1074 := by
    push_cast; rw [sub_mul, sub_mul, hK, hbm]
  refine sub_exact a b ha hb (K - m) (1022 + e) (by omega) h1.symm ?_
  have h2 : (value a.toBits - value b.toBits) * 2 ^ 1074 < 2 ^ 53 * 2 ^ (1022 + e) := by
    rw [show (2 : ℝ) ^ 53 * 2 ^ (1022 + e) = 2 ^ (e + 1) * 2 ^ 1074 by
      rw [← pow_add, ← pow_add]; congr 1; omega]
    exact mul_lt_mul_of_pos_right (by linarith) (by positivity)
  have h3 : 0 ≤ ((K - m : ℤ) : ℝ) := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hP
    rw [h1] at this
    have : 0 ≤ (value a.toBits - value b.toBits) * 2 ^ 1074 := mul_nonneg (by linarith) (by positivity)
    linarith
  rw [abs_of_nonneg h3]
  rw [← h1] at h2
  exact (lt_of_mul_lt_mul_right h2 hP.le).le

/-- `xh - 1/2` is exact for `4 ≤ xh < 256`. -/
theorem half_sub (x : Float) (hx : Finite x.toBits) (h4 : 4 ≤ value x.toBits)
    (h256 : value x.toBits < 256) :
    Finite (x - 0.5).toBits ∧ value (x - 0.5).toBits = value x.toBits - 1 / 2 := by
  rw [← TgammaTiny.half_value]
  have hhv := TgammaTiny.half_value
  have hhf := TgammaTiny.half_finite
  have key : ∀ e : ℕ, 2 ≤ e → e ≤ 7 → (2 : ℝ) ^ e ≤ value x.toBits → value x.toBits < 2 ^ (e + 1) →
      Finite (x - 0.5).toBits ∧ value (x - 0.5).toBits = value x.toBits - value (0.5 : Float).toBits := by
    intro e he2 he7 hlo hhi
    refine sub_exact_binade x 0.5 hx hhf e (by omega) hlo hhi (by rw [hhv]; norm_num)
      (by rw [hhv]; linarith) (2 ^ (51 - e)) ?_
    rw [hhv]
    push_cast
    rw [show (1 : ℝ) / 2 * 2 ^ 1074 = 2 ^ 1073 by norm_num, ← pow_add]
    congr 1
    omega
  rcases lt_or_ge (value x.toBits) 8 with h8 | h8
  · exact key 2 le_rfl (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases lt_or_ge (value x.toBits) 16 with h16 | h16
  · exact key 3 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases lt_or_ge (value x.toBits) 32 with h32 | h32
  · exact key 4 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases lt_or_ge (value x.toBits) 64 with h64 | h64
  · exact key 5 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases lt_or_ge (value x.toBits) 128 with h128 | h128
  · exact key 6 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  · exact key 7 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; linarith)

/-- `lh - 1` is exact for `1 ≤ lh < 8`. -/
theorem one_sub (x : Float) (hx : Finite x.toBits) (h1 : 1 ≤ value x.toBits)
    (h8 : value x.toBits < 8) :
    Finite (x - 1.0).toBits ∧ value (x - 1.0).toBits = value x.toBits - 1 := by
  rw [← one_value]
  have key : ∀ e : ℕ, e ≤ 2 → (2 : ℝ) ^ e ≤ value x.toBits → value x.toBits < 2 ^ (e + 1) →
      Finite (x - 1.0).toBits ∧ value (x - 1.0).toBits = value x.toBits - value (1.0 : Float).toBits := by
    intro e he2 hlo hhi
    refine sub_exact_binade x 1.0 hx one_finite e (by omega) hlo hhi (by rw [one_value]; norm_num)
      (by rw [one_value]; linarith) (2 ^ (52 - e)) ?_
    rw [one_value]
    push_cast
    rw [one_mul, ← pow_add]
    congr 1
    omega
  rcases lt_or_ge (value x.toBits) 2 with h2 | h2
  · exact key 0 (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  rcases lt_or_ge (value x.toBits) 4 with h4 | h4
  · exact key 1 (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
  · exact key 2 le_rfl (by norm_num; linarith) (by norm_num; linarith)

/-- **The first product** of `asLgammaAsym`. -/
theorem asym_prod (hF : FmaSpec.FmaNearest) (xh xl lh ll dz : Float) (hxh : Finite xh.toBits)
    (hxl : Finite xl.toBits) (hlh : Finite lh.toBits) (hll : Finite ll.toBits)
    (hdz : Finite dz.toBits) (h4 : 4 ≤ value xh.toBits) (h186 : value xh.toBits ≤ 186)
    (hxlb : |value xl.toBits| ≤ 1 / 2 ^ 44) (hlh1 : 13 / 10 ≤ value lh.toBits)
    (hlh2 : value lh.toBits ≤ 53 / 10)
    (hllb : |value ll.toBits| ≤ 1 / 2 ^ 22 + |value lh.toBits| / 2 ^ 52)
    (hdzb : |value dz.toBits| ≤ 1 / 2 ^ 45) :
    Finite (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).1.toBits ∧
      Finite (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).2.toBits ∧
      |value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).1.toBits +
          value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).2.toBits -
          (value xh.toBits - 1 / 2 + value xl.toBits) *
            (value lh.toBits + value ll.toBits + value dz.toBits - 1)| ≤ 1 / 2 ^ 63 ∧
      |value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).2.toBits| ≤ 73 / 100 / 2 ^ 14 ∧
      |value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).1.toBits| ≤ 1000 := by
  obtain ⟨hhf, hhv⟩ := half_sub xh hxh h4 (by linarith)
  obtain ⟨hof, hov⟩ := one_sub lh hlh (by linarith) (by linarith)
  -- `ll + dz`
  have hll' : |value ll.toBits| ≤ 1 / 2 ^ 22 + 53 / 10 / 2 ^ 52 := by
    have : |value lh.toBits| ≤ 53 / 10 := abs_le.mpr ⟨by linarith, hlh2⟩
    have : |value lh.toBits| / 2 ^ 52 ≤ 53 / 10 / 2 ^ 52 := div_le_div_of_nonneg_right this (by norm_num)
    linarith
  have hs := fapprox_add (fapprox_self ll hll) (fapprox_self dz hdz)
    (1 / 2 ^ 22 + 53 / 10 / 2 ^ 52 + 1 / 2 ^ 45)
    (by rw [add_zero, add_zero]; linarith [abs_add_le (value ll.toBits) (value dz.toBits)])
    (by norm_num)
  have hse : |value (ll + dz).toBits - (value ll.toBits + value dz.toBits)| ≤ 1 / 2 ^ 74 := by
    have := hs.2; linarith [(by norm_num : (0 : ℝ) + 0 + (1 / 2 ^ 22 + 53 / 10 / 2 ^ 52 + 1 / 2 ^ 45) /
      2 ^ 53 ≤ 1 / 2 ^ 74)]
  have hsb : |value (ll + dz).toBits| ≤ 1 / 2 ^ 22 * (1 + 1 / 2 ^ 22) := by
    have := abs_sub_abs_le_abs_sub (value (ll + dz).toBits) (value ll.toBits + value dz.toBits)
    linarith [abs_add_le (value ll.toBits) (value dz.toBits), (by norm_num : (1 : ℝ) / 2 ^ 22 +
      53 / 10 / 2 ^ 52 + 1 / 2 ^ 45 + 1 / 2 ^ 74 ≤ 1 / 2 ^ 22 * (1 + 1 / 2 ^ 22))]
  -- the product
  have hxa : |value (xh - 0.5).toBits| ≤ 371 / 2 := by
    rw [hhv, abs_le]; constructor <;> linarith
  have hla : |value (lh - 1.0).toBits| ≤ 43 / 10 := by
    rw [hov, abs_le]; constructor <;> linarith
  obtain ⟨h1, h2, he, hlow, hhigh⟩ := mulDD_spec hF (xh - 0.5) xl (lh - 1.0) (ll + dz) hhf hxl hof
    hs.1 (43 / 10 * (371 / 2)) (43 / 10 * (1 / 2 ^ 44)) (1 / 2 ^ 22 * (1 + 1 / 2 ^ 22) * (371 / 2))
    (1 / 2 ^ 22 * (1 + 1 / 2 ^ 22) * (1 / 2 ^ 44))
    (mul_le_mul hla hxa (abs_nonneg _) (by norm_num)) (mul_le_mul hla hxlb (abs_nonneg _) (by norm_num))
    (mul_le_mul hsb hxa (abs_nonneg _) (by norm_num)) (mul_le_mul hsb hxlb (abs_nonneg _) (by norm_num))
    (by norm_num) (by norm_num)
  rw [hhv, hov] at he
  refine ⟨h1, h2, ?_, hlow.trans (by norm_num), hhigh.trans (by norm_num)⟩
  -- the rounding of `ll + dz` inside the product
  have hxlx : |value xh.toBits - 1 / 2 + value xl.toBits| ≤ 186 := by
    rw [abs_le]; constructor <;> linarith [(abs_le.mp hxlb).1, (abs_le.mp hxlb).2,
      (by norm_num : (1 : ℝ) / 2 ^ 44 ≤ 1)]
  have hdb : |(value xh.toBits - 1 / 2 + value xl.toBits) *
      (value (ll + dz).toBits - (value ll.toBits + value dz.toBits))| ≤ 186 * (1 / 2 ^ 74) := by
    rw [abs_mul]; exact mul_le_mul hxlx hse (abs_nonneg _) (by norm_num)
  have e1 := abs_add_le (value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).1.toBits +
      value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).2.toBits -
      (value xh.toBits - 1 / 2 + value xl.toBits) * (value lh.toBits - 1 + value (ll + dz).toBits))
    ((value xh.toBits - 1 / 2 + value xl.toBits) *
      (value (ll + dz).toBits - (value ll.toBits + value dz.toBits)))
  rw [show value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).1.toBits +
      value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).2.toBits -
      (value xh.toBits - 1 / 2 + value xl.toBits) * (value lh.toBits - 1 + value (ll + dz).toBits) +
      (value xh.toBits - 1 / 2 + value xl.toBits) *
        (value (ll + dz).toBits - (value ll.toBits + value dz.toBits)) =
      value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).1.toBits +
      value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).2.toBits -
      (value xh.toBits - 1 / 2 + value xl.toBits) *
        (value lh.toBits + value ll.toBits + value dz.toBits - 1) by ring] at e1
  have he' : |value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).1.toBits +
      value (mulDD (xh - 0.5) xl (lh - 1.0) (ll + dz)).2.toBits -
      (value xh.toBits - 1 / 2 + value xl.toBits) * (value lh.toBits - 1 + value (ll + dz).toBits)| ≤
      1 / 2 ^ 64 := he.trans (by norm_num)
  linarith [(by norm_num : (1 : ℝ) / 2 ^ 64 + 186 * (1 / 2 ^ 74) ≤ 1 / 2 ^ 63)]

#print axioms sub_exact_binade
#print axioms half_sub
#print axioms asym_prod

end Verified.Examples.TgammaAsym1
