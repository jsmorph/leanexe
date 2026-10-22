import Library.Numerics.Float64.Lgamma.LgammaPiece10Base

/-!
The kernel check `pos_3` of piece 10 of `cr_lgamma`'s piecewise polynomial (`LgammaPiece10`).  Each
module holds checks of at most 62,000 coefficient operations in the Python model, since modules
with more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece10E

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece10Base

theorem pos_3 : ddRelOk cfg_pos
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (2129272986664967 / 11258999068426240) (304083684556801 / 1407374883553280)
        (912938248437763 / 5629499534213120)
    (PolyBound.shift (2129272986664967 / 11258999068426240) q10) (1) εin10 εout
        (129473995225 / 2 ^ 38) 2 = true := by
  decide +kernel

#print axioms pos_3

end Library.Numerics.Float64.Lgamma.LgammaPiece10E
