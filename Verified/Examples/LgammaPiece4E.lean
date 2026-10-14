import Verified.Examples.LgammaPiece4Base

/-!
The kernel checks `pose_1` and `pose_2` of piece 4 of `cr_lgamma`'s piecewise polynomial
(`LgammaPiece4`).  Each module holds checks of at most 62,000 coefficient operations in the Python
model, since modules with more stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaPiece4E

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece4Base

theorem pose_1 : ddRelOk cfg_pose
    ⟨1, 16, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (27487790694401 / 2 ^ 51) (27212912787457 / 1688849860263936)
        (28037546508289 / 3377699720527872)
    (PolyBound.shift (27487790694401 / 2 ^ 51) q4) (-1) εin4 εout (617096071515 / 2 ^ 40) 2 =
        true := by
  decide +kernel

theorem pose_2 : ddRelOk cfg_pose
    ⟨1, 16, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (135239930216453 / 6755399441055744) (26938034880513 / 2 ^ 50)
        (27212912787457 / 1688849860263936)
    (PolyBound.shift (135239930216453 / 6755399441055744) q4) (-1) εin4 εout (305100410029 / 2 ^ 39)
        3 = true := by
  decide +kernel

#print axioms pose_1
#print axioms pose_2

end Verified.Examples.LgammaPiece4E
