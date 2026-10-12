import Verified.Examples.TgammaPolySmall

/-!
A bound on CORE-MATH's accurate polynomial for `Γ x - 1/x` on `|x| < 1/4` (`tgamma.c` lines
306-345, commit `ff2f71f6`).  `accSmallList` holds the double-double `cc [0]` to `cc [27]` and the
doubles `c [0]` to `c [7]` of `Tgamma.accurateTable`.  `gamma_small_acc` bounds
`|Γ (1 + x) - (1 + x Q x)|` by `2 ^ -62` for `|x| ≤ 1/4`, with four pieces of radius `1/16`.
-/

namespace Verified.Examples.TgammaPolySmallAcc

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaThresholds
  TgammaFactsBase TgammaPolySmall

/-- The Taylor-model parameters: radius `1 / 16`, degree 18, 100 bits, at most 60 series terms with
remainder factor below `2 ^ -80`, and Mathlib's 20-digit bounds on `π`. -/
def cfg : Cfg := ⟨1 / 16, 18, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_pi : ((cfg.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg.piHi : ℚ) : ℝ) := pi_bounds20

theorem acc_piece0 : gammaPieceOk cfg ⟨(13 / 16), 16, log2Lo, log2Hi,
    ⟨4,
      (502333780715361158963212079627 / 10141204801825835211973625643008),
      (1004667561430722317926424159257 / 20282409603651670423947251286016)⟩,
    ⟨43,
      (1023077049366822522612182248553 / 5070602400912917605986812821504),
      (4092308197467290090448728994215 / 20282409603651670423947251286016)⟩⟩
    (PolyBound.shift (-3 / 16) (onePlusX accSmallList)) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem acc_piece1 : gammaPieceOk cfg ⟨(15 / 16), 16, log2Lo, log2Hi,
    ⟨4,
      (1154908319543312167760318508029 / 20282409603651670423947251286016),
      (1127840155804015788828436043 / 19807040628566084398385987584)⟩,
    ⟨44,
      (-416883011023939194528490066545 / 10141204801825835211973625643008),
      (-833766022047878389056980133087 / 20282409603651670423947251286016)⟩⟩
    (PolyBound.shift (-1 / 16) (onePlusX accSmallList)) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem acc_piece2 : gammaPieceOk cfg ⟨(17 / 16), 16, log2Lo, log2Hi,
    ⟨4,
      (652022178103848940236946226245 / 10141204801825835211973625643008),
      (1304044356207697880473892452493 / 20282409603651670423947251286016)⟩,
    ⟨44,
      (7741370438665620444991846248921 / 20282409603651670423947251286016),
      (1935342609666405111247961562231 / 5070602400912917605986812821504)⟩⟩
    (PolyBound.shift (1 / 16) (onePlusX accSmallList)) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem acc_piece3 : gammaPieceOk cfg ⟨(19 / 16), 16, log2Lo, log2Hi,
    ⟨4,
      (1452091798960694669864285438187 / 20282409603651670423947251286016),
      (726045899480347334932142719095 / 10141204801825835211973625643008)⟩,
    ⟨45,
      (1797393251636415067440274885261 / 20282409603651670423947251286016),
      (112337078227275941715017180329 / 1267650600228229401496703205376)⟩⟩
    (PolyBound.shift (3 / 16) (onePlusX accSmallList)) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem acc_cover : ∀ x : ℝ, ((-1 : ℝ) / 4) ≤ x → x ≤ ((-1 : ℝ) / 4) + 2 * ((1 : ℝ) / 16) * 4 →
    |Gamma ((1 : ℝ) + x) - eval (onePlusX accSmallList) x| ≤ 1 / 2 ^ 62 := by
  refine cover_pieces (K := 4) (by norm_num) (lo := ((-1 : ℝ) / 4)) (r := ((1 : ℝ) / 16))
    (by norm_num) (fun x => |Gamma ((1 : ℝ) + x) - eval (onePlusX accSmallList) x| ≤ 1 / 2 ^ 62) ?_
  intro j hj t ht
  interval_cases j
  · have hb := piece_bound cfg cfg_pi _ (onePlusX accSmallList) _ _ (1) (-3 / 16) (by norm_num)
      acc_piece0 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ (onePlusX accSmallList) _ _ (1) (-1 / 16) (by norm_num)
      acc_piece1 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ (onePlusX accSmallList) _ _ (1) (1 / 16) (by norm_num)
      acc_piece2 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ (onePlusX accSmallList) _ _ (1) (3 / 16) (by norm_num)
      acc_piece3 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num

/-- The accurate polynomial: `|Γ (1 + x) - (1 + x Q x)| ≤ 2 ^ -62` for `|x| ≤ 1/4`. -/
theorem gamma_small_acc : ∀ x : ℝ, |x| ≤ 1 / 4 →
    |Real.Gamma (1 + x) - (1 + x * eval accSmallList x)| ≤ 1 / 2 ^ 62 := by
  intro x hx
  have hx' := abs_le.mp hx
  rw [← eval_onePlusX]
  exact acc_cover x (by linarith) (by linarith)

/-- The relative form: `|Γ x - (1/x + Q x)| ≤ (5/3) 2 ^ -62 |Γ x|` for `0 < |x| ≤ 1/4`. -/
theorem gamma_sub_inv_acc {x : ℝ} (hx0 : x ≠ 0) (hx : |x| ≤ 1 / 4) :
    |Gamma x - (1 / x + eval accSmallList x)| ≤ 5 / 3 * (1 / 2 ^ 62) * |Gamma x| :=
  sub_inv_of_one_add hx0 hx (gamma_small_acc x hx)

#print axioms gamma_small_acc
#print axioms gamma_sub_inv_acc

end Verified.Examples.TgammaPolySmallAcc
