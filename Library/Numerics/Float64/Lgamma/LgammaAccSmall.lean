import Library.Numerics.Float64.Lgamma.LgammaAccSmallA
import Library.Numerics.Float64.Lgamma.LgammaAccSmallB
import Library.Numerics.Float64.Lgamma.LgammaAccSmallC
import Library.Numerics.Float64.Lgamma.LgammaAccSmallD
import Library.Numerics.Float64.Lgamma.LgammaAccSmallE
import Library.Numerics.Float64.Lgamma.LgammaAccSmallF
import Library.Numerics.Float64.Lgamma.LgammaAccSmallG
import Library.Numerics.Float64.Lgamma.LgammaAccSmallH
import Library.Numerics.Float64.Lgamma.LgammaAccSmallI
import Library.Numerics.Float64.Lgamma.LgammaAccSmallJ
import Library.Numerics.Float64.Lgamma.LgammaAccSmallK
import Library.Numerics.Float64.Lgamma.LgammaAccSmallL
import Library.Numerics.Float64.Lgamma.LgammaAccSmallM
import Library.Numerics.Float64.Lgamma.LgammaAccSmallN

/-!
`LgammaApprox.AccPolyFact`'s first clause: the accurate path's polynomial for `log Γ (1 + x)/x` on
`|x| ≤ 1/4` (`lgamma.c`, commit `ff2f71f6`) lies within `2 ^ -70` of the divided difference
`lgamma (1 + x)/x`.  Kernel checks of Taylor models of the divided difference (`GammaDD.ddPieceOk`)
in the check modules that this module imports, on an inner piece of radius `2 ^ -12` with 98 shifts
and eight outer pieces on each side, cover `2 ^ -75 ≤ |x| ≤ 1/4` (`side_neg`, `side_pos`), the
convexity of `log Γ` covers `|x| < 2 ^ -75` (`GammaDDCover.dd_abs_fact`), and `acc_small` gives the
statement's form.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccSmall

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaAccSmallBase
  LgammaAccSmallA LgammaAccSmallB LgammaAccSmallC LgammaAccSmallD LgammaAccSmallE LgammaAccSmallF
      LgammaAccSmallG LgammaAccSmallH LgammaAccSmallI LgammaAccSmallJ LgammaAccSmallK
      LgammaAccSmallL LgammaAccSmallM LgammaAccSmallN

theorem side_neg : ∀ s : ℝ, ((-1 : ℝ) / 4) ≤ s → s ≤ (0 : ℝ) → ((1 : ℝ) / 2 ^ 75) ≤ |s| →
    |(GammaBasic.lgamma ((1 : ℝ) + s) - GammaBasic.lgamma (1 : ℝ)) / s - eval accSmallList s| ≤ ((1 : ℝ) / 2 ^ 71) := by
  intro s h1 h2 hτ
  rcases le_or_gt s ((-1 : ℝ) / 2048) with hc | hc
  · refine cover_pieces (K := 8) (by norm_num) (lo := ((-1 : ℝ) / 4)) (r := ((511 : ℝ) / 2 ^ 15))
      (by norm_num)
          (fun s => |(GammaBasic.lgamma ((1 : ℝ) + s) - GammaBasic.lgamma (1 : ℝ)) / s - eval accSmallList s| ≤
          ((1 : ℝ) / 2 ^ 71)) ?_ s (by norm_num; linarith) (by norm_num; linarith)
    intro k hk t ht
    interval_cases k
    · have e : ((-1 : ℝ) / 4) + ((511 : ℝ) / 2 ^ 15) * (2 * ((0 : ℕ) : ℝ) + 1) + t =
          (((-7681 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-7681 / 2 ^ 15) (1 / 4) (3585 / 2 ^ 14) 0 neg_0 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 4) + ((511 : ℝ) / 2 ^ 15) * (2 * ((1 : ℕ) : ℝ) + 1) + t =
          (((-6659 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-6659 / 2 ^ 15) (3585 / 2 ^ 14) (1537 / 2 ^ 13) 0 neg_1 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 4) + ((511 : ℝ) / 2 ^ 15) * (2 * ((2 : ℕ) : ℝ) + 1) + t =
          (((-5637 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-5637 / 2 ^ 15) (1537 / 2 ^ 13) (2563 / 2 ^ 14) 0 neg_2 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 4) + ((511 : ℝ) / 2 ^ 15) * (2 * ((3 : ℕ) : ℝ) + 1) + t =
          (((-4615 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-4615 / 2 ^ 15) (2563 / 2 ^ 14) (513 / 4096) 0 neg_3 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 4) + ((511 : ℝ) / 2 ^ 15) * (2 * ((4 : ℕ) : ℝ) + 1) + t =
          (((-3593 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-3593 / 2 ^ 15) (513 / 4096) (1541 / 2 ^ 14) 0 neg_4 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 4) + ((511 : ℝ) / 2 ^ 15) * (2 * ((5 : ℕ) : ℝ) + 1) + t =
          (((-2571 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-2571 / 2 ^ 15) (1541 / 2 ^ 14) (515 / 2 ^ 13) 0 neg_5 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 4) + ((511 : ℝ) / 2 ^ 15) * (2 * ((6 : ℕ) : ℝ) + 1) + t =
          (((-1549 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-1549 / 2 ^ 15) (515 / 2 ^ 13) (519 / 2 ^ 14) 0 neg_6 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-1 : ℝ) / 4) + ((511 : ℝ) / 2 ^ 15) * (2 * ((7 : ℕ) : ℝ) + 1) + t =
          (((-527 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 17 _ (-527 / 2 ^ 15) (519 / 2 ^ 14) (1 / 2048) 0 neg_7 t ht
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

theorem side_pos : ∀ s : ℝ, (0 : ℝ) ≤ s → s ≤ ((1 : ℝ) / 4) → ((1 : ℝ) / 2 ^ 75) ≤ |s| →
    |(GammaBasic.lgamma ((1 : ℝ) + s) - GammaBasic.lgamma (1 : ℝ)) / s - eval accSmallList s| ≤ ((1 : ℝ) / 2 ^ 71) := by
  intro s h1 h2 hτ
  rcases le_or_gt ((1 : ℝ) / 2048) s with hc | hc
  · refine cover_pieces (K := 8) (by norm_num) (lo := ((1 : ℝ) / 2048)) (r := ((511 : ℝ) / 2 ^ 15))
      (by norm_num)
          (fun s => |(GammaBasic.lgamma ((1 : ℝ) + s) - GammaBasic.lgamma (1 : ℝ)) / s - eval accSmallList s| ≤
          ((1 : ℝ) / 2 ^ 71)) ?_ s (by norm_num; linarith) (by norm_num; linarith)
    intro k hk t ht
    interval_cases k
    · have e : ((1 : ℝ) / 2048) + ((511 : ℝ) / 2 ^ 15) * (2 * ((0 : ℕ) : ℝ) + 1) + t =
          (((527 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 17 _ (527 / 2 ^ 15) (519 / 2 ^ 14) (1 / 2048) 0 pos_0 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((511 : ℝ) / 2 ^ 15) * (2 * ((1 : ℕ) : ℝ) + 1) + t =
          (((1549 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (1549 / 2 ^ 15) (515 / 2 ^ 13) (519 / 2 ^ 14) 0 pos_1 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((511 : ℝ) / 2 ^ 15) * (2 * ((2 : ℕ) : ℝ) + 1) + t =
          (((2571 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (2571 / 2 ^ 15) (1541 / 2 ^ 14) (515 / 2 ^ 13) 0 pos_2 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((511 : ℝ) / 2 ^ 15) * (2 * ((3 : ℕ) : ℝ) + 1) + t =
          (((3593 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (3593 / 2 ^ 15) (513 / 4096) (1541 / 2 ^ 14) 0 pos_3 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((511 : ℝ) / 2 ^ 15) * (2 * ((4 : ℕ) : ℝ) + 1) + t =
          (((4615 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (4615 / 2 ^ 15) (2563 / 2 ^ 14) (513 / 4096) 0 pos_4 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((511 : ℝ) / 2 ^ 15) * (2 * ((5 : ℕ) : ℝ) + 1) + t =
          (((5637 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (5637 / 2 ^ 15) (1537 / 2 ^ 13) (2563 / 2 ^ 14) 0 pos_5 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((511 : ℝ) / 2 ^ 15) * (2 * ((6 : ℕ) : ℝ) + 1) + t =
          (((6659 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (6659 / 2 ^ 15) (3585 / 2 ^ 14) (1537 / 2 ^ 13) 0 pos_6 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((511 : ℝ) / 2 ^ 15) * (2 * ((7 : ℕ) : ℝ) + 1) + t =
          (((7681 / 2 ^ 15) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 16 _ (7681 / 2 ^ 15) (1 / 4) (3585 / 2 ^ 14) 0 pos_7 t ht
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
    check (subP accSmallList [accSmallList.headD 0]) (-(1 / 2 ^ 75)) (1 / 2 ^ 75) (1 / 2 ^ 75) 0 =
        true := by
  decide +kernel

theorem eval_zero_eq (p : List ℚ) : eval p 0 = ((p.headD 0 : ℚ) : ℝ) := by
  cases p <;> simp

theorem var_bound : ∀ s : ℝ, |s| ≤ ((1 : ℝ) / 2 ^ 75) → |eval accSmallList s - eval accSmallList 0|
    ≤ ((1 : ℝ) / 2 ^ 75) := by
  intro s hs
  have h := check_sound _ _ _ _ _ var_check s (by push_cast; linarith [(abs_le.mp hs).1])
    (by push_cast; linarith [(abs_le.mp hs).2])
  rw [eval_zero_eq]
  rw [eval_subP] at h
  simpa using h

/-- The bound on the divided difference over the whole interval, `0` excluded. -/
theorem dd_bound : ∀ s : ℝ, ((-1 : ℝ) / 4) ≤ s → s ≤ ((1 : ℝ) / 4) → s ≠ 0 →
    |(GammaBasic.lgamma ((1 : ℝ) + s) - GammaBasic.lgamma (1 : ℝ)) / s - eval accSmallList s| ≤ ((1 : ℝ) / 2 ^ 70) := by
  intro s h1 h2 hs0
  have hτ : (0 : ℝ) < ((1 : ℝ) / 2 ^ 75) := by norm_num
  have h := dd_abs_fact (x0 := (1 : ℝ)) (lo := ((-1 : ℝ) / 4)) (hi := ((1 : ℝ) / 4))
    (by norm_num) hτ (by norm_num) (by norm_num) (by norm_num) (eval accSmallList)
    (fun s h1 h2 => side_neg s h1 (by linarith) (by rw [abs_of_neg (by linarith)]; linarith))
    (fun s h1 h2 => side_pos s (by linarith) h2 (by rw [abs_of_pos (by linarith)]; linarith))
    var_bound s h1 h2 hs0
  exact h.trans (by norm_num)

/-- `LgammaApprox.AccPolyFact`'s first clause over `accSmallList`:
`|lgamma (1 + x) - x P (x)| ≤ 2 ^ -70 |x|` for `|x| ≤ 1/4`. -/
theorem acc_small : ∀ x : ℝ, |x| ≤ 1 / 4 →
    |GammaBasic.lgamma (1 + x) - x * eval accSmallList x| ≤ 1 / 2 ^ 70 * |x| := by
  intro x hx
  rcases eq_or_ne x 0 with h0 | h0
  · subst h0
    simp [lgamma_one]
  have hb := dd_bound x (by linarith [(abs_le.mp hx).1]) (by linarith [(abs_le.mp hx).2]) h0
  rw [lgamma_one, sub_zero] at hb
  have e : GammaBasic.lgamma (1 + x) - x * eval accSmallList x =
      x * (GammaBasic.lgamma (1 + x) / x - eval accSmallList x) := by
    rw [mul_sub, mul_comm x (GammaBasic.lgamma (1 + x) / x), div_mul_cancel₀ _ h0]
  rw [e, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hb (abs_nonneg x)

#print axioms side_neg
#print axioms side_pos
#print axioms dd_bound

end Library.Numerics.Float64.Lgamma.LgammaAccSmall
