import Library.Numerics.Float64.Lgamma.LgammaPiece4Base

/-!
The kernel checks `negc` and `posc` and `pose_0` of piece 4 of `cr_lgamma`'s piecewise polynomial
(`LgammaPiece4`).  Each module holds checks of at most 62,000 coefficient operations in the Python
model, since modules with more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece4D

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece4Base

theorem negc : ddRelOk cfg_negc
    ⟨1, 70, log2Lo, log2Hi,
      ⟨6, (2105249084996818464594150988857 / 2 ^ 104),
        (526312271249204616148537747215 / 2 ^ 102)⟩⟩
    (-1 / 4096) (1 / 2048) (1 / 2 ^ 69)
    (PolyBound.shift (-1 / 4096) q4) (-1) εin4 εout (631482058617 / 2 ^ 40) 0 = true := by
  decide +kernel

theorem posc : ddRelOk cfg_posc
    ⟨1, 70, log2Lo, log2Hi,
      ⟨6, (2105249084996818464594150988857 / 2 ^ 104),
        (526312271249204616148537747215 / 2 ^ 102)⟩⟩
    (1 / 4096) (1 / 2048) (1 / 2 ^ 69)
    (PolyBound.shift (1 / 4096) q4) (-1) εin4 εout (631042812261 / 2 ^ 40) 0 = true := by
  decide +kernel

theorem pose_0 : ddRelOk cfg_pose
    ⟨1, 16, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (29686813949953 / 6755399441055744) (28037546508289 / 3377699720527872) (1 / 2048)
    (PolyBound.shift (29686813949953 / 6755399441055744) q4) (-1) εin4 εout (624043130225 / 2 ^ 40)
        1 = true := by
  decide +kernel

#print axioms negc
#print axioms posc
#print axioms pose_0

end Library.Numerics.Float64.Lgamma.LgammaPiece4D
