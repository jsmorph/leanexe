import Verified.Examples.LgammaSmallFactA
import Verified.Examples.LgammaSmallFactB
import Verified.Examples.LgammaSmallFactC
import Verified.Examples.LgammaSmallFactD

/-!
`LgammaApprox.SmallFact`: CORE-MATH's polynomial for `log Γ (1 + x)/x` on `|x| ≤ 1/32` (`lgamma.c`
lines 919-925, commit `ff2f71f6`) lies within `2 ^ -70` of the divided difference
`lgamma (1 + x)/x`.  Kernel checks of Taylor models of the divided difference (`GammaDD.ddPieceOk`)
in the check modules that this module imports, on an inner piece of radius `2 ^ -12` with 98 shifts
and four outer pieces on each side, cover `2 ^ -75 ≤ |x| ≤ 1/32` (`side_neg`, `side_pos`), the
convexity of `log Γ` covers `|x| < 2 ^ -75` (`GammaDDCover.dd_abs_fact`), and `small_fact` gives
the statement's form.
-/

namespace Verified.Examples.LgammaSmallFact

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaSmallFactBase
  LgammaSmallFactA LgammaSmallFactB LgammaSmallFactC LgammaSmallFactD

theorem side_neg : ∀ s : ℝ, ((-1 : ℝ) / 32) ≤ s → s ≤ (0 : ℝ) → ((1 : ℝ) / 2 ^ 75) ≤ |s| →
    |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval smallList s| ≤ ((1 : ℝ) / 2 ^ 71) := by
  intro s h1 h2 hτ
  rcases le_or_gt s ((-1 : ℝ) / 2048) with hc | hc
  · refine cover_pieces (K := 4) (by norm_num) (lo := ((-1 : ℝ) / 32)) (r := ((63 : ℝ) / 2 ^ 14))
      (by norm_num)
          (fun s => |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval smallList s| ≤
          ((1 : ℝ) / 2 ^ 71)) ?_ s (by norm_num; linarith) (by norm_num; linarith)
    intro k hk t ht
    interval_cases k
    · have e : ((-1 : ℝ) / 32) + ((63 : ℝ) / 2 ^ 14) * (2 * ((0 : ℕ) : ℝ) + 1) + t =
          (((-449 / 2 ^ 14) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-449 / 2 ^ 14) (1 / 32) (193 / 2 ^ 13) 1 neg_0 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 32) + ((63 : ℝ) / 2 ^ 14) * (2 * ((1 : ℕ) : ℝ) + 1) + t =
          (((-323 / 2 ^ 14) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-323 / 2 ^ 14) (193 / 2 ^ 13) (65 / 4096) 0 neg_1 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 32) + ((63 : ℝ) / 2 ^ 14) * (2 * ((2 : ℕ) : ℝ) + 1) + t =
          (((-197 / 2 ^ 14) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-197 / 2 ^ 14) (65 / 4096) (67 / 2 ^ 13) 0 neg_2 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 32) + ((63 : ℝ) / 2 ^ 14) * (2 * ((3 : ℕ) : ℝ) + 1) + t =
          (((-71 / 2 ^ 14) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 17 _ (-71 / 2 ^ 14) (67 / 2 ^ 13) (1 / 2048) 0 neg_3 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  · have ht : |s - ((-1 : ℝ) / 4096)| ≤ ((1 : ℝ) / 4096) := by
      rw [abs_le]
      constructor <;> norm_num <;> linarith
    have e : (((-1 / 4096) : ℚ) : ℝ) + (s - ((-1 : ℝ) / 4096)) = s := by
      push_cast
      ring
    have h := piece_negc 98 _ (-1 / 4096) (1 / 2048) (1 / 2 ^ 75) 0 negc (s - ((-1 : ℝ) / 4096)) ht
        (by rw [e]; push_cast at hτ ⊢; exact hτ)
    rw [e] at h
    exact h

theorem side_pos : ∀ s : ℝ, (0 : ℝ) ≤ s → s ≤ ((1 : ℝ) / 32) → ((1 : ℝ) / 2 ^ 75) ≤ |s| →
    |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval smallList s| ≤ ((1 : ℝ) / 2 ^ 71) := by
  intro s h1 h2 hτ
  rcases le_or_gt ((1 : ℝ) / 2048) s with hc | hc
  · refine cover_pieces (K := 4) (by norm_num) (lo := ((1 : ℝ) / 2048)) (r := ((63 : ℝ) / 2 ^ 14))
      (by norm_num)
          (fun s => |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval smallList s| ≤
          ((1 : ℝ) / 2 ^ 71)) ?_ s (by norm_num; linarith) (by norm_num; linarith)
    intro k hk t ht
    interval_cases k
    · have e : ((1 : ℝ) / 2048) + ((63 : ℝ) / 2 ^ 14) * (2 * ((0 : ℕ) : ℝ) + 1) + t =
          (((71 / 2 ^ 14) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 17 _ (71 / 2 ^ 14) (67 / 2 ^ 13) (1 / 2048) 0 pos_0 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((63 : ℝ) / 2 ^ 14) * (2 * ((1 : ℕ) : ℝ) + 1) + t =
          (((197 / 2 ^ 14) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (197 / 2 ^ 14) (65 / 4096) (67 / 2 ^ 13) 0 pos_1 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((63 : ℝ) / 2 ^ 14) * (2 * ((2 : ℕ) : ℝ) + 1) + t =
          (((323 / 2 ^ 14) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (323 / 2 ^ 14) (193 / 2 ^ 13) (65 / 4096) 0 pos_2 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((63 : ℝ) / 2 ^ 14) * (2 * ((3 : ℕ) : ℝ) + 1) + t =
          (((449 / 2 ^ 14) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (449 / 2 ^ 14) (1 / 32) (193 / 2 ^ 13) 1 pos_3 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  · have ht : |s - ((1 : ℝ) / 4096)| ≤ ((1 : ℝ) / 4096) := by
      rw [abs_le]
      constructor <;> norm_num <;> linarith
    have e : (((1 / 4096) : ℚ) : ℝ) + (s - ((1 : ℝ) / 4096)) = s := by
      push_cast
      ring
    have h := piece_posc 98 _ (1 / 4096) (1 / 2048) (1 / 2 ^ 75) 0 posc (s - ((1 : ℝ) / 4096)) ht
        (by rw [e]; push_cast at hτ ⊢; exact hτ)
    rw [e] at h
    exact h

theorem var_check :
    check (subP smallList [smallList.headD 0]) (-(1 / 2 ^ 75)) (1 / 2 ^ 75) (1 / 2 ^ 75) 0 = true :=
        by
  decide +kernel

theorem eval_zero_eq (p : List ℚ) : eval p 0 = ((p.headD 0 : ℚ) : ℝ) := by
  cases p <;> simp

theorem var_bound : ∀ s : ℝ, |s| ≤ ((1 : ℝ) / 2 ^ 75) → |eval smallList s - eval smallList 0| ≤
    ((1 : ℝ) / 2 ^ 75) := by
  intro s hs
  have h := check_sound _ _ _ _ _ var_check s (by push_cast; linarith [(abs_le.mp hs).1])
    (by push_cast; linarith [(abs_le.mp hs).2])
  rw [eval_zero_eq]
  rw [eval_subP] at h
  simpa using h

/-- The bound on the divided difference over the whole interval, `0` excluded. -/
theorem dd_bound : ∀ s : ℝ, ((-1 : ℝ) / 32) ≤ s → s ≤ ((1 : ℝ) / 32) → s ≠ 0 →
    |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval smallList s| ≤ ((1 : ℝ) / 2 ^ 70) := by
  intro s h1 h2 hs0
  have hτ : (0 : ℝ) < ((1 : ℝ) / 2 ^ 75) := by norm_num
  have h := dd_abs_fact (x0 := (1 : ℝ)) (lo := ((-1 : ℝ) / 32)) (hi := ((1 : ℝ) / 32))
    (by norm_num) hτ (by norm_num) (by norm_num) (by norm_num) (eval smallList)
    (fun s h1 h2 => side_neg s h1 (by linarith) (by rw [abs_of_neg (by linarith)]; linarith))
    (fun s h1 h2 => side_pos s (by linarith) h2 (by rw [abs_of_pos (by linarith)]; linarith))
    var_bound s h1 h2 hs0
  exact h.trans (by norm_num)

/-- `LgammaApprox.SmallFact` over `smallList`:
`|lgamma (1 + x) - x P (x)| ≤ 2 ^ -70 |x|` for `|x| ≤ 1/32`. -/
theorem small_fact : ∀ x : ℝ, |x| ≤ 1 / 32 →
    |lgamma (1 + x) - x * eval smallList x| ≤ 1 / 2 ^ 70 * |x| := by
  intro x hx
  rcases eq_or_ne x 0 with h0 | h0
  · subst h0
    simp [lgamma_one]
  have hb := dd_bound x (by linarith [(abs_le.mp hx).1]) (by linarith [(abs_le.mp hx).2]) h0
  rw [lgamma_one, sub_zero] at hb
  have e : lgamma (1 + x) - x * eval smallList x =
      x * (lgamma (1 + x) / x - eval smallList x) := by
    rw [mul_sub, mul_comm x (lgamma (1 + x) / x), div_mul_cancel₀ _ h0]
  rw [e, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hb (abs_nonneg x)

#print axioms side_neg
#print axioms side_pos
#print axioms dd_bound

end Verified.Examples.LgammaSmallFact
