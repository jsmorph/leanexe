import Verified.Examples.LgammaAccSmallBase

/-!
The kernel checks `neg_4` and `neg_5` of `LgammaAccSmall`.  Each module holds checks of at most
62,000 coefficient operations in the Python model, since modules of divided-difference checks with
more stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaAccSmallE

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaAccSmallBase

theorem neg_4 : ddPieceOk cfg_neg
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (-3593 / 2 ^ 15) (513 / 4096) (1541 / 2 ^ 14)
    (PolyBound.shift (-3593 / 2 ^ 15) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

theorem neg_5 : ddPieceOk cfg_neg
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (-2571 / 2 ^ 15) (1541 / 2 ^ 14) (515 / 2 ^ 13)
    (PolyBound.shift (-2571 / 2 ^ 15) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

#print axioms neg_4
#print axioms neg_5

end Verified.Examples.LgammaAccSmallE
