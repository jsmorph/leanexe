import Verified.Examples.LgammaAccSmallBase

/-!
The kernel check `pos_5` of `LgammaAccSmall`.  Each module holds checks of at most 62,000
coefficient operations in the Python model, since modules of divided-difference checks with more
stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaAccSmallK

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaAccSmallBase

theorem pos_5 : ddPieceOk cfg_pos
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (5637 / 2 ^ 15) (1537 / 2 ^ 13) (2563 / 2 ^ 14)
    (PolyBound.shift (5637 / 2 ^ 15) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

#print axioms pos_5

end Verified.Examples.LgammaAccSmallK
