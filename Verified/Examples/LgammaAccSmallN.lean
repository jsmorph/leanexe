import Verified.Examples.LgammaAccSmallBase

/-!
The kernel check `posc` of `LgammaAccSmall`.  Each module holds checks of at most 62,000
coefficient operations in the Python model, since modules of divided-difference checks with more
stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaAccSmallN

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaAccSmallBase

theorem posc : ddPieceOk cfg_posc
    ⟨(1), 98, log2Lo, log2Hi,
      ⟨7,
        (-5210762243831560969561002273045 / 20282409603651670423947251286016),
        (-2605381121915780484780501136521 / 10141204801825835211973625643008)⟩⟩
    (1 / 4096) (1 / 2048) (1 / 2 ^ 75)
    (PolyBound.shift (1 / 4096) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

#print axioms posc

end Verified.Examples.LgammaAccSmallN
