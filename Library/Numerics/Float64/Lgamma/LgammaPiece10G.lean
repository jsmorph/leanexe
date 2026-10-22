import Library.Numerics.Float64.Lgamma.LgammaPiece10Base

/-!
The kernel check `pose_1` of piece 10 of `cr_lgamma`'s piecewise polynomial (`LgammaPiece10`).
Each module holds checks of at most 62,000 coefficient operations in the Python model, since
modules with more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece10G

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece10Base

theorem pose_1 : ddRelOk cfg_pose
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (2736065966243849 / 11258999068426240) (709299532376749 / 2814749767106560)
        (1317466901490351 / 5629499534213120)
    (PolyBound.shift (2736065966243849 / 11258999068426240) q10) (1) εin10 εout
        (135331085609 / 2 ^ 38) 2 = true := by
  decide +kernel

#print axioms pose_1

end Library.Numerics.Float64.Lgamma.LgammaPiece10G
