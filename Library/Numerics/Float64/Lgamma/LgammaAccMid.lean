import LeanExe.ProofKit.GammaFits
import Library.Numerics.Float64.Tgamma.TgammaFactsBase
import Library.Numerics.Float64.Lgamma.Compiled
import Library.Numerics.Float64.Tgamma.GammaPi

/-!
The accurate path's polynomial of `cr_lgamma` near `3/2` (`lgamma.c`, commit `ff2f71f6`), read
from `Lgamma.accurateTable` at words 68 to 127, within `2 ^ -70` of `log Γ (3/2 + d)` for
`|d| ≤ 1/4` (`acc_mid`).  Each of four pieces of radius `1/16` is checked by
`GammaFits.lgammaDiffOk` with the Taylor model of `lgamma`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccMid

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaThresholds
  TgammaFactsBase

/-- The polynomial: 30 double-double coefficients. -/
def accMidList : List ℚ := ddCoeffs Lgamma.accurateTable 68 30

/-- The Taylor-model parameters: radius `1/16`, degree 20, 100 bits, at most 60 series terms with
factor below `2 ^ -100`, and `π` within `2 ^ -128`. -/
def cfgM : Cfg := ⟨1 / 16, 20, 100, 60, 1 / 2 ^ 100, Library.Numerics.Float64.Tgamma.GammaPi.piLo128, Library.Numerics.Float64.Tgamma.GammaPi.piHi128⟩

theorem cfgM_pi : ((cfgM.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfgM.piHi : ℚ) : ℝ) := Library.Numerics.Float64.Tgamma.GammaPi.pi_bounds128

theorem m_0 : lgammaDiffOk cfgM ⟨(21 / 16), 15, log2Lo, log2Hi,
      ⟨4,
          (24520118458287268002627174227 / 1267650600228229401496703205376),
          (392321895332596288042034787635 / 20282409603651670423947251286016)⟩,
      ⟨42,
          (-4928907308848871278533335776179 / 20282409603651670423947251286016),
          (-308056706803054454908333486011 / 1267650600228229401496703205376)⟩⟩
    (.polyOf accMidList (.poly [(-3 / 16), 1])) (1 / 2 ^ 70) 0 = true := by
  decide +kernel

theorem m_1 : lgammaDiffOk cfgM ⟨(23 / 16), 15, log2Lo, log2Hi,
      ⟨4,
          (273575100701882645664555789073 / 10141204801825835211973625643008),
          (547150201403765291329111578149 / 20282409603651670423947251286016)⟩,
      ⟨42,
          (2304093651501992663816639682955 / 20282409603651670423947251286016),
          (1152046825750996331908319841479 / 10141204801825835211973625643008)⟩⟩
    (.polyOf accMidList (.poly [(-1 / 16), 1])) (1 / 2 ^ 70) 0 = true := by
  decide +kernel

theorem m_2 : lgammaDiffOk cfgM ⟨(25 / 16), 15, log2Lo, log2Hi,
      ⟨4,
          (350402777249855875209961874077 / 10141204801825835211973625643008),
          (700805554499711750419923748157 / 20282409603651670423947251286016)⟩,
      ⟨43,
          (-75249873332893251223464004779 / 316912650057057350374175801344),
          (-4815991893305168078301696305853 / 20282409603651670423947251286016)⟩⟩
    (.polyOf accMidList (.poly [(1 / 16), 1])) (1 / 2 ^ 70) 0 = true := by
  decide +kernel

theorem m_3 : lgammaDiffOk cfgM ⟨(27 / 16), 15, log2Lo, log2Hi,
      ⟨4,
          (106663199157778369728635808885 / 2535301200456458802993406410752),
          (853305593262226957829086471083 / 20282409603651670423947251286016)⟩,
      ⟨43,
          (1861175226219333920406473905625 / 20282409603651670423947251286016),
          (465293806554833480101618476407 / 5070602400912917605986812821504)⟩⟩
    (.polyOf accMidList (.poly [(3 / 16), 1])) (1 / 2 ^ 70) 0 = true := by
  decide +kernel

theorem acc_mid : ∀ d : ℝ, |d| ≤ 1 / 4 → |lgamma (3 / 2 + d) - eval accMidList d| ≤ 1 / 2 ^ 70 := by
  have hc := cover_pieces (K := 4) (by norm_num) (lo := (5 / 4 : ℝ)) (r := (1 / 16 : ℝ))
    (by norm_num) (fun x => |lgamma x - eval accMidList (x - 3 / 2)| ≤ 1 / 2 ^ 70) ?_
  · intro d hd
    have hd' := abs_le.mp hd
    have h := hc (3 / 2 + d) (by linarith) (by norm_num; linarith)
    simp only [add_sub_cancel_left] at h
    exact h
  intro j hj t ht
  interval_cases j
  · have h := lgammaDiffOk_sound cfgM _ _ _ _ cfgM_pi m_0 (t := t)
      (by simp only [cfgM]; push_cast; exact ht)
    simp only [TaylorModel.Expr.eval, eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one,
      mul_one] at h
    convert h using 4 <;> push_cast <;> ring
  · have h := lgammaDiffOk_sound cfgM _ _ _ _ cfgM_pi m_1 (t := t)
      (by simp only [cfgM]; push_cast; exact ht)
    simp only [TaylorModel.Expr.eval, eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one,
      mul_one] at h
    convert h using 4 <;> push_cast <;> ring
  · have h := lgammaDiffOk_sound cfgM _ _ _ _ cfgM_pi m_2 (t := t)
      (by simp only [cfgM]; push_cast; exact ht)
    simp only [TaylorModel.Expr.eval, eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one,
      mul_one] at h
    convert h using 4 <;> push_cast <;> ring
  · have h := lgammaDiffOk_sound cfgM _ _ _ _ cfgM_pi m_3 (t := t)
      (by simp only [cfgM]; push_cast; exact ht)
    simp only [TaylorModel.Expr.eval, eval_cons, eval_nil, mul_zero, add_zero, Rat.cast_one,
      mul_one] at h
    convert h using 4 <;> push_cast <;> ring

#print axioms acc_mid

end Library.Numerics.Float64.Lgamma.LgammaAccMid
