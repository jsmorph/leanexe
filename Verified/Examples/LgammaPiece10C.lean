import Verified.Examples.LgammaPiece10Base

/-!
The kernel checks `pos_0` and `pos_1` of piece 10 of `cr_lgamma`'s piecewise polynomial
(`LgammaPiece10`).  Each module holds checks of at most 62,000 coefficient operations in the Python
model, since modules with more stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaPiece10C

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece10Base

theorem pos_0 : ddRelOk cfg_pos
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (308894047928321 / 11258999068426240) (306145268858881 / 5629499534213120) (1 / 2048)
    (PolyBound.shift (308894047928321 / 11258999068426240) q10) (1) εin10 εout
        (462704251009 / 2 ^ 40) 3 = true := by
  decide +kernel

theorem pos_1 : ddRelOk cfg_pos
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (915687027507203 / 11258999068426240) (304770879324161 / 2814749767106560)
        (306145268858881 / 5629499534213120)
    (PolyBound.shift (915687027507203 / 11258999068426240) q10) (1) εin10 εout
        (60187853915 / 2 ^ 37) 2 = true := by
  decide +kernel

#print axioms pos_0
#print axioms pos_1

end Verified.Examples.LgammaPiece10C
