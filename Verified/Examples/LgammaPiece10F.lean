import Verified.Examples.LgammaPiece10Base

/-!
The kernel check `pose_0` of piece 10 of `cr_lgamma`'s piecewise polynomial (`LgammaPiece10`).
Each module holds checks of at most 62,000 coefficient operations in the Python model, since
modules with more stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaPiece10F

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece10Base

theorem pose_0 : ddRelOk cfg_pose
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (506760327943511 / 2 ^ 51) (1317466901490351 / 5629499534213120)
        (304083684556801 / 1407374883553280)
    (PolyBound.shift (506760327943511 / 2 ^ 51) q10) (1) εin10 εout (267763488507 / 2 ^ 39) 1 =
        true := by
  decide +kernel

#print axioms pose_0

end Verified.Examples.LgammaPiece10F
