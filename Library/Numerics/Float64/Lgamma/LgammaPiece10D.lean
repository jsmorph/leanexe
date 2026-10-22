import Library.Numerics.Float64.Lgamma.LgammaPiece10Base

/-!
The kernel check `pos_2` of piece 10 of `cr_lgamma`'s piecewise polynomial (`LgammaPiece10`).  Each
module holds checks of at most 62,000 coefficient operations in the Python model, since modules
with more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece10D

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece10Base

theorem pos_2 : ddRelOk cfg_pos
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (304496001417217 / 2 ^ 51) (912938248437763 / 5629499534213120)
        (304770879324161 / 2814749767106560)
    (PolyBound.shift (304496001417217 / 2 ^ 51) q10) (1) εin10 εout (31243361321 / 2 ^ 36) 2 =
        true := by
  decide +kernel

#print axioms pos_2

end Library.Numerics.Float64.Lgamma.LgammaPiece10D
