import Verified.Examples.LgammaSmallFactBase

/-!
The kernel checks `neg_3` and `negc` and `pos_0` of `LgammaSmallFact`.  Each module holds checks of
at most 62,000 coefficient operations in the Python model, since modules of divided-difference
checks with more stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaSmallFactB

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaSmallFactBase

theorem neg_3 : ddPieceOk cfg_neg
    ⟨(1), 17, log2Lo, log2Hi,
      ⟨4,
        (2388923773544278907367941202429 / 20282409603651670423947251286016),
        (4665866745203669740953010161 / 39614081257132168796771975168)⟩⟩
    (-71 / 2 ^ 14) (67 / 2 ^ 13) (1 / 2048)
    (PolyBound.shift (-71 / 2 ^ 14) smallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

theorem negc : ddPieceOk cfg_negc
    ⟨(1), 98, log2Lo, log2Hi,
      ⟨7,
        (-5210762243831560969561002273045 / 20282409603651670423947251286016),
        (-2605381121915780484780501136521 / 10141204801825835211973625643008)⟩⟩
    (-1 / 4096) (1 / 2048) (1 / 2 ^ 75)
    (PolyBound.shift (-1 / 4096) smallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

theorem pos_0 : ddPieceOk cfg_pos
    ⟨(1), 17, log2Lo, log2Hi,
      ⟨4,
        (2388923773544278907367941202429 / 20282409603651670423947251286016),
        (4665866745203669740953010161 / 39614081257132168796771975168)⟩⟩
    (71 / 2 ^ 14) (67 / 2 ^ 13) (1 / 2048)
    (PolyBound.shift (71 / 2 ^ 14) smallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

#print axioms neg_3
#print axioms negc
#print axioms pos_0

end Verified.Examples.LgammaSmallFactB
