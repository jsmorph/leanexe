import Verified.Examples.TgammaFactsBase

/-!
A bound on CORE-MATH's fast polynomial for `Γ x - 1/x` on `|x| < 1/4` (`tgamma.c` lines 682-706,
commit `ff2f71f6`).  `smallList` holds the double-double `cc [0]` to `cc [4]` and the doubles
`c [0]` to `c [15]` of `Tgamma.smallTable`; `polyddd` adds `x · (c [0] + ⋯)` to the coefficient
of degree 4.  Since `Γ x - 1/x = (Γ (1 + x) - 1)/x`, `gamma_small_fast` bounds
`|Γ (1 + x) - (1 + x Q x)|` by `2 ^ -60` for `|x| ≤ 1/4`, with four pieces of radius `1/16` and
sixteen shifts each.  `Γ (1 + x) ≥ 3/5` there (`gamma_one_add_ge`), and `sub_inv_of_one_add` turns
a bound `e` on `Γ (1 + x)` into the relative bound `(5/3) e` on `Γ x` for `x ≠ 0`.
-/

namespace Verified.Examples.TgammaPolySmall

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaThresholds
  TgammaFactsBase

/-- The Taylor-model parameters: radius `1 / 16`, degree 18, 100 bits, at most 60 series terms with
remainder factor below `2 ^ -80`, and Mathlib's 20-digit bounds on `π`. -/
def cfg : Cfg := ⟨1 / 16, 18, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_pi : ((cfg.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg.piHi : ℚ) : ℝ) := pi_bounds20

theorem fast_piece0 : gammaPieceOk cfg ⟨(13 / 16), 16, log2Lo, log2Hi,
    ⟨4,
      (502333780715361158963212079627 / 10141204801825835211973625643008),
      (1004667561430722317926424159257 / 20282409603651670423947251286016)⟩,
    ⟨43,
      (1023077049366822522612182248553 / 5070602400912917605986812821504),
      (4092308197467290090448728994215 / 20282409603651670423947251286016)⟩⟩
    (PolyBound.shift (-3 / 16) (onePlusX smallList)) (1 / 2 ^ 60) 3 = true := by
  decide +kernel

theorem fast_piece1 : gammaPieceOk cfg ⟨(15 / 16), 16, log2Lo, log2Hi,
    ⟨4,
      (1154908319543312167760318508029 / 20282409603651670423947251286016),
      (1127840155804015788828436043 / 19807040628566084398385987584)⟩,
    ⟨44,
      (-416883011023939194528490066545 / 10141204801825835211973625643008),
      (-833766022047878389056980133087 / 20282409603651670423947251286016)⟩⟩
    (PolyBound.shift (-1 / 16) (onePlusX smallList)) (1 / 2 ^ 60) 1 = true := by
  decide +kernel

theorem fast_piece2 : gammaPieceOk cfg ⟨(17 / 16), 16, log2Lo, log2Hi,
    ⟨4,
      (652022178103848940236946226245 / 10141204801825835211973625643008),
      (1304044356207697880473892452493 / 20282409603651670423947251286016)⟩,
    ⟨44,
      (7741370438665620444991846248921 / 20282409603651670423947251286016),
      (1935342609666405111247961562231 / 5070602400912917605986812821504)⟩⟩
    (PolyBound.shift (1 / 16) (onePlusX smallList)) (1 / 2 ^ 60) 1 = true := by
  decide +kernel

theorem fast_piece3 : gammaPieceOk cfg ⟨(19 / 16), 16, log2Lo, log2Hi,
    ⟨4,
      (1452091798960694669864285438187 / 20282409603651670423947251286016),
      (726045899480347334932142719095 / 10141204801825835211973625643008)⟩,
    ⟨45,
      (1797393251636415067440274885261 / 20282409603651670423947251286016),
      (112337078227275941715017180329 / 1267650600228229401496703205376)⟩⟩
    (PolyBound.shift (3 / 16) (onePlusX smallList)) (1 / 2 ^ 60) 3 = true := by
  decide +kernel

theorem fast_cover : ∀ x : ℝ, ((-1 : ℝ) / 4) ≤ x → x ≤ ((-1 : ℝ) / 4) + 2 * ((1 : ℝ) / 16) * 4 →
    |Gamma ((1 : ℝ) + x) - eval (onePlusX smallList) x| ≤ 1 / 2 ^ 60 := by
  refine cover_pieces (K := 4) (by norm_num) (lo := ((-1 : ℝ) / 4)) (r := ((1 : ℝ) / 16))
    (by norm_num) (fun x => |Gamma ((1 : ℝ) + x) - eval (onePlusX smallList) x| ≤ 1 / 2 ^ 60) ?_
  intro j hj t ht
  interval_cases j
  · have hb := piece_bound cfg cfg_pi _ (onePlusX smallList) _ _ (1) (-3 / 16) (by norm_num)
      fast_piece0 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ (onePlusX smallList) _ _ (1) (-1 / 16) (by norm_num)
      fast_piece1 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ (onePlusX smallList) _ _ (1) (1 / 16) (by norm_num)
      fast_piece2 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ (onePlusX smallList) _ _ (1) (3 / 16) (by norm_num)
      fast_piece3 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num

theorem gamma_one_add_ge {x : ℝ} (hx : |x| ≤ 1 / 4) : 3 / 5 ≤ Gamma (1 + x) := by
  have hx' := abs_le.mp hx
  rcases eq_or_ne x 0 with h0 | h0
  · rw [h0, add_zero, Gamma_one]
    norm_num
  · obtain ⟨h1, h2⟩ := GammaBasic.gamma_sub_inv_bounds h0 (by linarith) (by linarith)
    have hg : Gamma (1 + x) = 1 + x * (Gamma x - 1 / x) := by
      rw [add_comm 1 x, Gamma_add_one h0, mul_sub, mul_one_div_cancel h0]
      ring
    rw [hg]
    rcases le_or_gt 0 x with hp | hn
    · nlinarith [mul_nonneg hp (by linarith : (0 : ℝ) ≤ Gamma x - 1 / x + 8 / 5)]
    · nlinarith [mul_nonneg_of_nonpos_of_nonpos hn.le h2]

theorem sub_inv_of_one_add {x q e : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 4)
    (h : |Gamma (1 + x) - (1 + x * q)| ≤ e) :
    |Gamma x - (1 / x + q)| ≤ 5 / 3 * e * |Gamma x| := by
  have hg := gamma_one_add_ge hx
  have hG : Gamma (1 + x) = x * Gamma x := by rw [add_comm, Gamma_add_one hx0]
  have hxa : 0 < |x| := abs_pos.mpr hx0
  have he : Gamma x - (1 / x + q) = (Gamma (1 + x) - (1 + x * q)) / x := by
    rw [hG]
    field_simp
  rw [he, abs_div, div_le_iff₀ hxa]
  have hGx : |Gamma (1 + x)| = |x| * |Gamma x| := by rw [hG, abs_mul]
  have hge : 3 / 5 ≤ |x| * |Gamma x| := by rw [← hGx, abs_of_pos (by linarith)]; exact hg
  have he0 : 0 ≤ e := (abs_nonneg _).trans h
  nlinarith [mul_le_mul_of_nonneg_left hge he0]

/-- The fast polynomial: `|Γ (1 + x) - (1 + x Q x)| ≤ 2 ^ -60` for `|x| ≤ 1/4`. -/
theorem gamma_small_fast : ∀ x : ℝ, |x| ≤ 1 / 4 →
    |Real.Gamma (1 + x) - (1 + x * eval smallList x)| ≤ 1 / 2 ^ 60 := by
  intro x hx
  have hx' := abs_le.mp hx
  rw [← eval_onePlusX]
  exact fast_cover x (by linarith) (by linarith)

/-- The relative form: `|Γ x - (1/x + Q x)| ≤ (5/3) 2 ^ -60 |Γ x|` for `0 < |x| ≤ 1/4`. -/
theorem gamma_sub_inv_fast {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 4) :
    |Gamma x - (1 / x + eval smallList x)| ≤ 5 / 3 * (1 / 2 ^ 60) * |Gamma x| :=
  sub_inv_of_one_add hx0 hx (gamma_small_fast x hx)

#print axioms gamma_small_fast
#print axioms gamma_sub_inv_fast

end Verified.Examples.TgammaPolySmall
