import Library.Numerics.Float64.Lgamma.LgammaPiece4A
import Library.Numerics.Float64.Lgamma.LgammaPiece4B
import Library.Numerics.Float64.Lgamma.LgammaPiece4C
import Library.Numerics.Float64.Lgamma.LgammaPiece4D
import Library.Numerics.Float64.Lgamma.LgammaPiece4E

/-!
Piece 4 of `cr_lgamma`'s piecewise polynomial (`lgamma.c` lines 759-870, commit `ff2f71f6`), which
contains the zero 1 of `lgamma` and carries the factor `1 - x`: on the piece widened by `2 ^ -50`
at each end, `|lgamma x - (1 - x) pieceP 4 (x - off 4)| ≤ 12 · 10 ^ -20 |lgamma x|` (`piece4`).
With `s = x - 1`, `lgamma x = s g s` for the divided difference `g`, and `Q = q4` of
`LgammaPiece4Base` has `(1 - x) pieceP 4 (x - off 4) = s Q s`.  Kernel checks of Taylor models of
`g` (`GammaRel.ddRelOk`) bound `g - Q` relative to `g` for `|s| ≥ 2 ^ -69`, and the convexity of
`lgamma` (`GammaDDCover.dd_rel_center`) covers `|s| < 2 ^ -69`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece4

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece4Base
  LgammaPiece4A LgammaPiece4B LgammaPiece4C LgammaPiece4D LgammaPiece4E

theorem side_neg : ∀ s : ℝ, ((-135033771786241 : ℝ) / 2 ^ 50) ≤ s → s ≤ (0 : ℝ) → ((1 : ℝ) / 2 ^ 69)
    ≤ |s| →
    |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval q4 s| ≤ εout *
        |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s| := by
  intro s hlo hhi hτ
  rcases le_or_gt s ((-405651071172611 : ℝ) / 2 ^ 52) with hhi | hlo
  · refine cover_pieces (K := 3) (by norm_num) (lo := ((-135033771786241 : ℝ) / 2 ^ 50))
      (r := ((134484015972353 : ℝ) / 27021597764222976))
      (by norm_num)
          (fun s => |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval q4 s| ≤ εout *
          |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s|) ?_ s (by norm_num; linarith)
          (by norm_num; linarith)
    intro k hk t ht
    interval_cases k
    · have e : ((-135033771786241 : ℝ) / 2 ^ 50) + ((134484015972353 : ℝ) / 27021597764222976) *
        (2 * ((0 : ℕ) : ℝ) + 1) + t =
          (((-3106326506897431 / 27021597764222976) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_nege 16 _ (-3106326506897431 / 27021597764222976) (135033771786241 / 2 ^ 50)
          (1485921245462539 / 13510798882111488) (-1) (736173735345 / 2 ^ 40) 3 nege_0 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-135033771786241 : ℝ) / 2 ^ 50) + ((134484015972353 : ℝ) / 27021597764222976) *
        (2 * ((1 : ℕ) : ℝ) + 1) + t =
          (((-945786158317575 / 2 ^ 53) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_nege 16 _ (-945786158317575 / 2 ^ 53) (1485921245462539 / 13510798882111488)
          (675718614745093 / 6755399441055744) (-1) (726191780533 / 2 ^ 40) 2 nege_1 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-135033771786241 : ℝ) / 2 ^ 50) + ((134484015972353 : ℝ) / 27021597764222976) *
        (2 * ((2 : ℕ) : ℝ) + 1) + t =
          (((-2568390443008019 / 27021597764222976) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_nege 16 _ (-2568390443008019 / 27021597764222976)
          (675718614745093 / 6755399441055744) (405651071172611 / 2 ^ 52) (-1)
          (716317418111 / 2 ^ 40) 1 nege_2 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  rcases le_or_gt s ((-1 : ℝ) / 2048) with hhi | hlo
  · refine cover_pieces (K := 3) (by norm_num) (lo := ((-405651071172611 : ℝ) / 2 ^ 52))
      (r := ((134484015972353 : ℝ) / 2 ^ 53))
      (by norm_num)
          (fun s => |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval q4 s| ≤ εout *
          |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s|) ?_ s (by norm_num; linarith)
          (by norm_num; linarith)
    intro k hk t ht
    interval_cases k
    · have e : ((-405651071172611 : ℝ) / 2 ^ 52) + ((134484015972353 : ℝ) / 2 ^ 53) *
        (2 * ((0 : ℕ) : ℝ) + 1) + t =
          (((-676818126372869 / 2 ^ 53) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-676818126372869 / 2 ^ 53) (405651071172611 / 2 ^ 52)
          (135583527600129 / 2 ^ 51) (-1) (687316471523 / 2 ^ 40) 3 neg_0 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-405651071172611 : ℝ) / 2 ^ 52) + ((134484015972353 : ℝ) / 2 ^ 53) *
        (2 * ((1 : ℕ) : ℝ) + 1) + t =
          (((-407850094428163 / 2 ^ 53) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-407850094428163 / 2 ^ 53) (135583527600129 / 2 ^ 51)
          (136683039227905 / 2 ^ 52) (-1) (659202703727 / 2 ^ 40) 3 neg_1 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
    · have e : ((-405651071172611 : ℝ) / 2 ^ 52) + ((134484015972353 : ℝ) / 2 ^ 53) *
        (2 * ((2 : ℕ) : ℝ) + 1) + t =
          (((-138882062483457 / 2 ^ 53) : ℚ) : ℝ) + t := by
        norm_num
      rw [e]
      exact piece_neg 16 _ (-138882062483457 / 2 ^ 53) (136683039227905 / 2 ^ 52) (1 / 2048) (-1)
          (631921513997 / 2 ^ 40) 3 neg_2 t ht
        (le_abs.mpr (Or.inr (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  have ht : |s - ((-1 : ℝ) / 4096)| ≤ ((1 : ℝ) / 4096) := by
    rw [abs_le]
    constructor <;> norm_num <;> linarith
  have e : (((-1 / 4096) : ℚ) : ℝ) + (s - ((-1 : ℝ) / 4096)) = s := by
    push_cast
    ring
  have h := piece_negc 70 _ (-1 / 4096) (1 / 2048) (1 / 2 ^ 69) (-1) (631482058617 / 2 ^ 40) 0 negc
      (s - ((-1 : ℝ) / 4096)) ht
    (by rw [e]; push_cast at hτ ⊢; exact hτ)
  rw [e] at h
  exact h

theorem side_pos : ∀ s : ℝ, (0 : ℝ) ≤ s → s ≤ ((26938034880513 : ℝ) / 2 ^ 50) → ((1 : ℝ) / 2 ^ 69) ≤
    |s| →
    |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval q4 s| ≤ εout *
        |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s| := by
  intro s hlo hhi hτ
  rcases le_or_gt s ((1 : ℝ) / 2048) with hhi | hlo
  · have ht : |s - ((1 : ℝ) / 4096)| ≤ ((1 : ℝ) / 4096) := by
      rw [abs_le]
      constructor <;> norm_num <;> linarith
    have e : (((1 / 4096) : ℚ) : ℝ) + (s - ((1 : ℝ) / 4096)) = s := by
      push_cast
      ring
    have h := piece_posc 70 _ (1 / 4096) (1 / 2048) (1 / 2 ^ 69) (-1) (631042812261 / 2 ^ 40) 0 posc
        (s - ((1 : ℝ) / 4096)) ht
      (by rw [e]; push_cast at hτ ⊢; exact hτ)
    rw [e] at h
    exact h
  refine cover_pieces (K := 3) (by norm_num) (lo := ((1 : ℝ) / 2048))
      (r := ((26388279066625 : ℝ) / 6755399441055744))
    (by norm_num)
        (fun s => |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval q4 s| ≤ εout *
        |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s|) ?_ s (by norm_num; linarith)
        (by norm_num; linarith)
  intro k hk t ht
  interval_cases k
  · have e : ((1 : ℝ) / 2048) + ((26388279066625 : ℝ) / 6755399441055744) * (2 * ((0 : ℕ) : ℝ) + 1)
      + t =
        (((29686813949953 / 6755399441055744) : ℚ) : ℝ) + t := by
      norm_num
    rw [e]
    exact piece_pose 16 _ (29686813949953 / 6755399441055744) (28037546508289 / 3377699720527872)
        (1 / 2048) (-1) (624043130225 / 2 ^ 40) 1 pose_0 t ht
      (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  · have e : ((1 : ℝ) / 2048) + ((26388279066625 : ℝ) / 6755399441055744) * (2 * ((1 : ℕ) : ℝ) + 1)
      + t =
        (((27487790694401 / 2 ^ 51) : ℚ) : ℝ) + t := by
      norm_num
    rw [e]
    exact piece_pose 16 _ (27487790694401 / 2 ^ 51) (27212912787457 / 1688849860263936)
        (28037546508289 / 3377699720527872) (-1) (617096071515 / 2 ^ 40) 2 pose_1 t ht
      (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))
  · have e : ((1 : ℝ) / 2048) + ((26388279066625 : ℝ) / 6755399441055744) * (2 * ((2 : ℕ) : ℝ) + 1)
      + t =
        (((135239930216453 / 6755399441055744) : ℚ) : ℝ) + t := by
      norm_num
    rw [e]
    exact piece_pose 16 _ (135239930216453 / 6755399441055744) (26938034880513 / 2 ^ 50)
        (27212912787457 / 1688849860263936) (-1) (305100410029 / 2 ^ 39) 3 pose_2 t ht
      (le_abs.mpr (Or.inl (by have h := abs_le.mp ht; norm_num; linarith [h.1, h.2])))

theorem var_check :
    check (subP q4 [q4.headD 0]) (-((1 / 2 ^ 69))) (1 / 2 ^ 69) (1 / 2 ^ 69) 0 = true := by
  decide +kernel

theorem eval_zero_eq (p : List ℚ) : eval p 0 = ((p.headD 0 : ℚ) : ℝ) := by
  cases p <;> simp

theorem var_bound : ∀ s : ℝ, |s| ≤ ((1 : ℝ) / 2 ^ 69) → |eval q4 s - eval q4 0| ≤
    ((1 : ℝ) / 2 ^ 69) := by
  intro s hs
  have h := check_sound _ _ _ _ _ var_check s (by push_cast; linarith [(abs_le.mp hs).1])
    (by push_cast; linarith [(abs_le.mp hs).2])
  rw [eval_zero_eq]
  rw [eval_subP] at h
  simpa using h

/-- `Q` at `τ` and `-τ`, within `2 ^ -100` of rationals. -/
theorem q_p : check (subP q4 [(-749268770891330209175789384453265 / 2 ^ 110)]) (1 / 2 ^ 69)
    (1 / 2 ^ 69) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

theorem q_m : check (subP q4 [(-374634385445665104589703316360057 / 2 ^ 109)]) (-((1 / 2 ^ 69)))
    (-((1 / 2 ^ 69))) (1 / 2 ^ 100) 0 = true := by
  decide +kernel

/-- The relative bound on the divided difference over the widened piece, `0` excluded. -/
theorem dd_rel : ∀ s : ℝ, ((-135033771786241 : ℝ) / 2 ^ 50) ≤ s → s ≤
    ((26938034880513 : ℝ) / 2 ^ 50) → s ≠ 0 →
    |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s - eval q4 s| ≤
      12 / 10 ^ 20 * |(lgamma ((1 : ℝ) + s) - lgamma (1 : ℝ)) / s| := by
  have hsp := check_sound _ _ _ _ _ q_p ((1 : ℝ) / 2 ^ 69) (by norm_num) (by norm_num)
  have hsm := check_sound _ _ _ _ _ q_m (-((1 : ℝ) / 2 ^ 69)) (by norm_num) (by norm_num)
  rw [eval_subP] at hsp hsm
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at hsp hsm
  push_cast at hsp hsm
  exact dd_rel_fact (x0 := (1 : ℝ)) (lo := ((-135033771786241 : ℝ) / 2 ^ 50))
      (hi := ((26938034880513 : ℝ) / 2 ^ 50)) (τ := ((1 : ℝ) / 2 ^ 69))
    (ε := εout) (εf := 12 / 10 ^ 20) (V := ((1 : ℝ) / 2 ^ 69))
        (m := ((665484352860916857 : ℝ) / 2 ^ 60)) (M := ((332742176430458431 : ℝ) / 2 ^ 59))
    (Qm := ((166371088215229215 : ℝ) / 2 ^ 58)) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [εout]) (by norm_num [εout]) (eval q4)
    (fun s h1 h2 => side_neg s h1 (by linarith) (by rw [abs_of_neg (by linarith)]; linarith))
    (fun s h1 h2 => side_pos s (by linarith) h2 (by rw [abs_of_pos (by linarith)]; linarith))
    var_bound
    (by rw [abs_le] at hsp ⊢; constructor <;> norm_num at hsp ⊢ <;> linarith [hsp.1, hsp.2])
    (by rw [abs_le] at hsm ⊢; constructor <;> norm_num at hsm ⊢ <;> linarith [hsm.1, hsm.2])
    (by norm_num [εout])
        (Or.inl (by have := (abs_le.mp hsp).2; norm_num [εout] at this ⊢; linarith))
        (by norm_num [εout]) (by norm_num [εout])

/-- Piece 4 of `PieceFact`. -/
theorem piece4 : ∀ x : ℝ, (border 4 : ℝ) - 1 / 2 ^ 50 ≤ x → x ≤ (border 5 : ℝ) + 1 / 2 ^ 50 →
    |lgamma x - (1 - x) * eval (pieceP 4) (x - off 4)| ≤ 12 / 10 ^ 20 * |lgamma x| := by
  intro x h1 h2
  have hb1 : border 4 = (14419 / 2 ^ 14) := by decide +kernel
  have hb2 : border 5 = (2097 / 2048) := by decide +kernel
  rw [hb1] at h1
  rw [hb2] at h2
  push_cast at h1 h2
  rcases eq_or_ne (x - 1) 0 with h0 | h0
  · have hx : x = 1 := by linarith
    subst hx
    norm_num [lgamma_one]
  have hd := dd_rel (x - 1) (by norm_num; linarith) (by norm_num; linarith) h0
  rw [show (1 : ℝ) + (x - 1) = x by ring, lgamma_one, sub_zero] at hd
  have hq : eval q4 (x - 1) = -eval (pieceP 4) (x - off 4) := by
    simp only [q4, eval_scaleP, eval_shift]
    push_cast
    ring_nf
  rw [hq] at hd
  have k1 : |lgamma x - (1 - x) * eval (pieceP 4) (x - off 4)| =
      |x - 1| * |lgamma x / (x - 1) - -eval (pieceP 4) (x - off 4)| := by
    rw [← abs_mul]
    congr 1
    rw [mul_sub, mul_comm (x - 1) (lgamma x / (x - 1)), div_mul_cancel₀ _ h0]
    ring
  have k2 : |lgamma x| = |x - 1| * |lgamma x / (x - 1)| := by
    rw [← abs_mul, mul_comm, div_mul_cancel₀ _ h0]
  rw [k1, k2]
  calc |x - 1| * |lgamma x / (x - 1) - -eval (pieceP 4) (x - off 4)|
      ≤ |x - 1| * (12 / 10 ^ 20 * |lgamma x / (x - 1)|) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg _)
    _ = 12 / 10 ^ 20 * (|x - 1| * |lgamma x / (x - 1)|) := by ring

#print axioms piece4

end Library.Numerics.Float64.Lgamma.LgammaPiece4
