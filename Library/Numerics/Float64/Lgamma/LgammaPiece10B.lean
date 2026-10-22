import Library.Numerics.Float64.Lgamma.LgammaPiece10Base

/-!
The kernel checks `nege_2` and `negc` and `posc` of piece 10 of `cr_lgamma`'s piecewise polynomial
(`LgammaPiece10`).  Each module holds checks of at most 62,000 coefficient operations in the Python
model, since modules with more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece10B

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece10Base

theorem nege_2 : ddRelOk cfg_nege
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (-22482722138795 / 2 ^ 51) (21932966324907 / 2 ^ 50) (1 / 2048)
    (PolyBound.shift (-22482722138795 / 2 ^ 51) q10) (1) εin10 εout (56953940321 / 2 ^ 37) 1 =
        true := by
  decide +kernel

theorem negc : ddRelOk cfg_negc
    ⟨2, 69, log2Lo, log2Hi,
      ⟨6, (2105249084996818464594150988857 / 2 ^ 104),
        (526312271249204616148537747215 / 2 ^ 102)⟩⟩
    (-1 / 4096) (1 / 2048) (1 / 2 ^ 69)
    (PolyBound.shift (-1 / 4096) q10) (1) εin10 εout (462359735895 / 2 ^ 40) 0 = true := by
  decide +kernel

theorem posc : ddRelOk cfg_posc
    ⟨2, 69, log2Lo, log2Hi,
      ⟨6, (2105249084996818464594150988857 / 2 ^ 104),
        (526312271249204616148537747215 / 2 ^ 102)⟩⟩
    (1 / 4096) (1 / 2048) (1 / 2 ^ 69)
    (PolyBound.shift (1 / 4096) q10) (1) εin10 εout (462532011019 / 2 ^ 40) 0 = true := by
  decide +kernel

#print axioms nege_2
#print axioms negc
#print axioms posc

end Library.Numerics.Float64.Lgamma.LgammaPiece10B
