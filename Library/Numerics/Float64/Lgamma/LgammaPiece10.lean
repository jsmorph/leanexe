import Library.Numerics.Float64.Lgamma.LgammaPiece10A
import Library.Numerics.Float64.Lgamma.LgammaPiece10B
import Library.Numerics.Float64.Lgamma.LgammaPiece10C
import Library.Numerics.Float64.Lgamma.LgammaPiece10D
import Library.Numerics.Float64.Lgamma.LgammaPiece10E
import Library.Numerics.Float64.Lgamma.LgammaPiece10F
import Library.Numerics.Float64.Lgamma.LgammaPiece10G
import Library.Numerics.Float64.Lgamma.LgammaPiece10H

/-!
Piece 10 of `cr_lgamma`'s piecewise polynomial (`lgamma.c` lines 759-870, commit `ff2f71f6`), which
contains the zero 2 of `lgamma` and carries the factor `x - 2`: on the piece widened by `2 ^ -50`
at each end, `|lgamma x - (x - 2) pieceP 10 (x - off 10)| ≤ 12 · 10 ^ -20 |lgamma x|` (`piece10`).
With `s = x - 2`, `lgamma x = s g s` for the divided difference `g`, and `Q = q10` of
`LgammaPiece10Base` has `(x - 2) pieceP 10 (x - off 10) = s Q s`.  Kernel checks of Taylor models
of `g` (`GammaRel.ddRelOk`) bound `g - Q` relative to `g` for `|s| ≥ 2 ^ -69`, and the convexity of
`lgamma` (`GammaDDCover.dd_rel_center`) covers `|s| < 2 ^ -69`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece10

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece10Base
  LgammaPiece10A LgammaPiece10B LgammaPiece10C LgammaPiece10D LgammaPiece10E LgammaPiece10F
      LgammaPiece10G LgammaPiece10H

theorem side_neg : ∀ s : ℝ, ((-64699387346945 : ℝ) / 2 ^ 50) ≤ s → s ≤ (0 : ℝ) → ((1 : ℝ) / 2 ^ 69)
    ≤ |s| →
    |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s - eval q10 s| ≤ εout *
        |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s| := by
  intro s hlo hhi hτ
  rcases le_or_gt s ((-1 : ℝ) / 2048) with hhi | hlo
  · refine cover_pieces (K := 3) (by norm_num) (lo := ((-64699387346945 : ℝ) / 2 ^ 50))
      (r := ((21383210511019 : ℝ) / 2 ^ 51))
      (by norm_num)
          (fun s => |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s - eval q10 s| ≤ εout *
          |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s|) ?_ s (by norm_num; linarith)
          (by norm_num; linarith)
    intro k hk t ht
    interval_cases k
    · have e : ((-64699387346945 : ℝ) / 2 ^ 50) + ((21383210511019 : ℝ) / 2 ^ 51) *
        (2 * ((0 : ℕ) : ℝ) + 1) + t =
          (((-108015564182871 / 2 ^ 51) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_nege 15 _ (-108015564182871 / 2 ^ 51) (64699387346945 / 2 ^ 50)
          (21658088417963 / 2 ^ 49) (1) (221005884173 / 2 ^ 39) 3 nege_0 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-64699387346945 : ℝ) / 2 ^ 50) + ((21383210511019 : ℝ) / 2 ^ 51) *
        (2 * ((1 : ℕ) : ℝ) + 1) + t =
          (((-65249143160833 / 2 ^ 51) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_nege 15 _ (-65249143160833 / 2 ^ 51) (21658088417963 / 2 ^ 49)
          (21932966324907 / 2 ^ 50) (1) (224424594225 / 2 ^ 39) 2 nege_1 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-64699387346945 : ℝ) / 2 ^ 50) + ((21383210511019 : ℝ) / 2 ^ 51) *
        (2 * ((2 : ℕ) : ℝ) + 1) + t =
          (((-22482722138795 / 2 ^ 51) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_nege 15 _ (-22482722138795 / 2 ^ 51) (21932966324907 / 2 ^ 50) (1 / 2048) (1)
          (56953940321 / 2 ^ 37) 1 nege_2 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  have ht : |s - ((-1 : ℝ) / 4096)| ≤ ((1 : ℝ) / 4096) := by
    rw [abs_le]
    constructor <;> norm_num <;> linarith
  have e : (((-1 / 4096) : ℚ) : ℝ) + (s - ((-1 : ℝ) / 4096)) = s := by
    push_cast
    ring
  have h := piece_negc 69 _ (-1 / 4096) (1 / 2048) (1 / 2 ^ 69) (1) (462359735895 / 2 ^ 40) 0 negc
      (s - ((-1 : ℝ) / 4096)) ht
    (by rw [e]; push_cast at hτ ⊢; exact hτ)
  rw [e] at h
  exact h

theorem side_pos : ∀ s : ℝ, (0 : ℝ) ≤ s → s ≤ ((303946245603329 : ℝ) / 2 ^ 50) → ((1 : ℝ) / 2 ^ 69)
    ≤ |s| →
    |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s - eval q10 s| ≤ εout *
        |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s| := by
  intro s hlo hhi hτ
  rcases le_or_gt s ((1 : ℝ) / 2048) with hhi | hlo
  · have ht : |s - ((1 : ℝ) / 4096)| ≤ ((1 : ℝ) / 4096) := by
      rw [abs_le]
      constructor <;> norm_num <;> linarith
    have e : (((1 / 4096) : ℚ) : ℝ) + (s - ((1 : ℝ) / 4096)) = s := by
      push_cast
      ring
    have h := piece_posc 69 _ (1 / 4096) (1 / 2048) (1 / 2 ^ 69) (1) (462532011019 / 2 ^ 40) 0 posc
        (s - ((1 : ℝ) / 4096)) ht
      (by rw [e]; push_cast at hτ ⊢; exact hτ)
    rw [e] at h
    exact h
  rcases le_or_gt s ((304083684556801 : ℝ) / 1407374883553280) with hhi | hlo
  · refine cover_pieces (K := 4) (by norm_num) (lo := ((1 : ℝ) / 2048))
      (r := ((303396489789441 : ℝ) / 11258999068426240))
      (by norm_num)
          (fun s => |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s - eval q10 s| ≤ εout *
          |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s|) ?_ s (by norm_num; linarith)
          (by norm_num; linarith)
    intro k hk t ht
    interval_cases k
    · have e : ((1 : ℝ) / 2048) + ((303396489789441 : ℝ) / 11258999068426240) *
        (2 * ((0 : ℕ) : ℝ) + 1) + t =
          (((308894047928321 / 11258999068426240) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 15 _ (308894047928321 / 11258999068426240)
          (306145268858881 / 5629499534213120) (1 / 2048) (1) (462704251009 / 2 ^ 40) 3 pos_0 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((303396489789441 : ℝ) / 11258999068426240) *
        (2 * ((1 : ℕ) : ℝ) + 1) + t =
          (((915687027507203 / 11258999068426240) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 15 _ (915687027507203 / 11258999068426240)
          (304770879324161 / 2814749767106560) (306145268858881 / 5629499534213120) (1)
          (60187853915 / 2 ^ 37) 2 pos_1 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((303396489789441 : ℝ) / 11258999068426240) *
        (2 * ((2 : ℕ) : ℝ) + 1) + t =
          (((304496001417217 / 2 ^ 51) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 15 _ (304496001417217 / 2 ^ 51) (912938248437763 / 5629499534213120)
          (304770879324161 / 2814749767106560) (1) (31243361321 / 2 ^ 36) 2 pos_2 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((1 : ℝ) / 2048) + ((303396489789441 : ℝ) / 11258999068426240) *
        (2 * ((3 : ℕ) : ℝ) + 1) + t =
          (((2129272986664967 / 11258999068426240) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_pos 15 _ (2129272986664967 / 11258999068426240)
          (304083684556801 / 1407374883553280) (912938248437763 / 5629499534213120) (1)
          (129473995225 / 2 ^ 38) 2 pos_3 t ht
        (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  refine cover_pieces (K := 3) (by norm_num) (lo := ((304083684556801 : ℝ) / 1407374883553280))
      (r := ((101132163263147 : ℝ) / 11258999068426240))
    (by norm_num)
        (fun s => |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s - eval q10 s| ≤ εout *
        |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s|) ?_ s (by norm_num; linarith)
        (by norm_num; linarith)
  intro k hk t ht
  interval_cases k
  · have e : ((304083684556801 : ℝ) / 1407374883553280) +
      ((101132163263147 : ℝ) / 11258999068426240) * (2 * ((0 : ℕ) : ℝ) + 1) + t =
        (((506760327943511 / 2 ^ 51) : ℚ) : ℝ) + t := by
      norm_num
    rw [e]
    exact piece_pose 15 _ (506760327943511 / 2 ^ 51) (1317466901490351 / 5629499534213120)
        (304083684556801 / 1407374883553280) (1) (267763488507 / 2 ^ 39) 1 pose_0 t ht
      (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  · have e : ((304083684556801 : ℝ) / 1407374883553280) +
      ((101132163263147 : ℝ) / 11258999068426240) * (2 * ((1 : ℕ) : ℝ) + 1) + t =
        (((2736065966243849 / 11258999068426240) : ℚ) : ℝ) + t := by
      norm_num
    rw [e]
    exact piece_pose 15 _ (2736065966243849 / 11258999068426240)
        (709299532376749 / 2814749767106560) (1317466901490351 / 5629499534213120) (1)
        (135331085609 / 2 ^ 38) 2 pose_1 t ht
      (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  · have e : ((304083684556801 : ℝ) / 1407374883553280) +
      ((101132163263147 : ℝ) / 11258999068426240) * (2 * ((2 : ℕ) : ℝ) + 1) + t =
        (((2938330292770143 / 11258999068426240) : ℚ) : ℝ) + t := by
      norm_num
    rw [e]
    exact piece_pose 15 _ (2938330292770143 / 11258999068426240) (303946245603329 / 2 ^ 50)
        (709299532376749 / 2814749767106560) (1) (547082864475 / 2 ^ 40) 3 pose_2 t ht
      (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))

theorem var_check :
    check (subP q10 [q10.headD 0]) (-((1 / 2 ^ 69))) (1 / 2 ^ 69) (1 / 2 ^ 70) 0 = true := by
  decide +kernel

theorem eval_zero_eq (p : List ℚ) : eval p 0 = ((p.headD 0 : ℚ) : ℝ) := by
  cases p <;> simp

theorem var_bound : ∀ s : ℝ, |s| ≤ ((1 : ℝ) / 2 ^ 69) → |eval q10 s - eval q10 0| ≤
    ((1 : ℝ) / 2 ^ 70) := by
  intro s hs
  have h := check_sound _ _ _ _ _ var_check s (by push_cast; linarith [(abs_le.mp hs).1])
    (by push_cast; linarith [(abs_le.mp hs).2])
  rw [eval_zero_eq]
  rw [eval_subP] at h
  simpa using h

/-- `Q` at `τ` and `-τ`, within `2 ^ -100` of rationals. -/
theorem q_p : check (subP q10 [(548805443742376697968592811440837 / 2 ^ 110)]) (1 / 2 ^ 69)
    (1 / 2 ^ 69) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem q_m : check (subP q10 [(548805443742376697967174586429541 / 2 ^ 110)]) (-((1 / 2 ^ 69)))
    (-((1 / 2 ^ 69))) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

/-- The relative bound on the divided difference over the widened piece, `0` excluded. -/
theorem dd_rel : ∀ s : ℝ, ((-64699387346945 : ℝ) / 2 ^ 50) ≤ s → s ≤
    ((303946245603329 : ℝ) / 2 ^ 50) → s ≠ 0 →
    |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s - eval q10 s| ≤
      12 / 10 ^ 20 * |(lgamma ((2 : ℝ) + s) - lgamma (2 : ℝ)) / s| := by
  have hsp := check_sound _ _ _ _ _ q_p ((1 : ℝ) / 2 ^ 69) (by norm_num) (by norm_num)
  have hsm := check_sound _ _ _ _ _ q_m (-((1 : ℝ) / 2 ^ 69)) (by norm_num) (by norm_num)
  rw [eval_subP] at hsp hsm
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at hsp hsm
  push_cast at hsp hsm
  exact dd_rel_fact (x0 := (2 : ℝ)) (lo := ((-64699387346945 : ℝ) / 2 ^ 50))
      (hi := ((303946245603329 : ℝ) / 2 ^ 50)) (τ := ((1 : ℝ) / 2 ^ 69))
    (ε := εout) (εf := 12 / 10 ^ 20) (V := ((1 : ℝ) / 2 ^ 70))
        (m := ((121859287936482529 : ℝ) / 2 ^ 58)) (M := ((487437151745930121 : ℝ) / 2 ^ 60))
    (Qm := ((487437151745930119 : ℝ) / 2 ^ 60)) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [εout]) (by norm_num [εout]) (eval q10)
    (fun s h1 h2 => side_neg s h1 (by linarith) (by rw [abs_of_neg (by linarith)]; linarith))
    (fun s h1 h2 => side_pos s (by linarith) h2 (by rw [abs_of_pos (by linarith)]; linarith))
    var_bound
    (by rw [abs_le] at hsp ⊢; constructor <;> norm_num at hsp ⊢ <;> linarith [hsp.1, hsp.2])
    (by rw [abs_le] at hsm ⊢; constructor <;> norm_num at hsm ⊢ <;> linarith [hsm.1, hsm.2])
    (by norm_num [εout])
        (Or.inr (by have := (abs_le.mp hsm).1; norm_num [εout] at this ⊢; linarith))
        (by norm_num [εout]) (by norm_num [εout])

/-- Piece 10 of `PieceFact`. -/
theorem piece10 : ∀ x : ℝ, (border 10 : ℝ) - 1 / 2 ^ 50 ≤ x → x ≤ (border 11 : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - (x - 2) * eval (pieceP 10) (x - off 10)| ≤ 12 / 10 ^ 20 * |lgamma x| := by
  intro x h1 h2
  have hb1 : border 10 = (63653 / 2 ^ 15) := by decide +kernel
  have hb2 : border 11 = (37191 / 2 ^ 14) := by decide +kernel
  rw [hb1] at h1
  rw [hb2] at h2
  push_cast at h1 h2
  rcases eq_or_ne (x - 2) 0 with h0 | h0
  · have hx : x = 2 := by linarith
    subst hx
    norm_num [lgamma_two]
  have hd := dd_rel (x - 2) (by norm_num; linarith) (by norm_num; linarith) h0
  rw [show (2 : ℝ) + (x - 2) = x by ring, lgamma_two, sub_zero] at hd
  have hq : eval q10 (x - 2) = eval (pieceP 10) (x - off 10) := by
    simp only [q10, eval_shift]
    push_cast
    ring_nf
  rw [hq] at hd
  have k1 : |lgamma x - (x - 2) * eval (pieceP 10) (x - off 10)| =
      |x - 2| * |lgamma x / (x - 2) - eval (pieceP 10) (x - off 10)| := by
    rw [← abs_mul]
    congr 1
    rw [mul_sub, mul_comm (x - 2) (lgamma x / (x - 2)), div_mul_cancel₀ _ h0]
  have k2 : |lgamma x| = |x - 2| * |lgamma x / (x - 2)| := by
    rw [← abs_mul, mul_comm, div_mul_cancel₀ _ h0]
  rw [k1, k2]
  calc |x - 2| * |lgamma x / (x - 2) - eval (pieceP 10) (x - off 10)|
      ≤ |x - 2| * (12 / 10 ^ 20 * |lgamma x / (x - 2)|) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ = 12 / 10 ^ 20 * (|x - 2| * |lgamma x / (x - 2)|) := by ring

#print axioms piece10

end Library.Numerics.Float64.Lgamma.LgammaPiece10
