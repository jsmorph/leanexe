import Verified.Examples.LgammaPiece10Base

/-!
The kernel check `pose_2` of piece 10 of `cr_lgamma`'s piecewise polynomial (`LgammaPiece10`).
Each module holds checks of at most 62,000 coefficient operations in the Python model, since
modules with more stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaPiece10H

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece10Base

theorem pose_2 : ddRelOk cfg_pose
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (2938330292770143 / 11258999068426240) (303946245603329 / 2 ^ 50)
        (709299532376749 / 2814749767106560)
    (PolyBound.shift (2938330292770143 / 11258999068426240) q10) (1) εin10 εout
        (547082864475 / 2 ^ 40) 3 = true := by
  decide +kernel

#print axioms pose_2

end Verified.Examples.LgammaPiece10H
