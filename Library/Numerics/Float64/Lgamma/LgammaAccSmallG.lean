import Library.Numerics.Float64.Lgamma.LgammaAccSmallBase

/-!
The kernel checks `negc` and `pos_0` of `LgammaAccSmall`.  Each module holds checks of at most
62,000 coefficient operations in the Python model, since modules of divided-difference checks with
more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccSmallG

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaAccSmallBase

theorem negc : ddPieceOk cfg_negc
    ⟨(1), 98, log2Lo, log2Hi,
      ⟨7,
        (-5210762243831560969561002273045 / 20282409603651670423947251286016),
        (-2605381121915780484780501136521 / 10141204801825835211973625643008)⟩⟩
    (-1 / 4096) (1 / 2048) (1 / 2 ^ 75)
    (PolyBound.shift (-1 / 4096) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

theorem pos_0 : ddPieceOk cfg_pos
    ⟨(1), 17, log2Lo, log2Hi,
      ⟨4,
        (2388923773544278907367941202429 / 20282409603651670423947251286016),
        (4665866745203669740953010161 / 39614081257132168796771975168)⟩⟩
    (527 / 2 ^ 15) (519 / 2 ^ 14) (1 / 2048)
    (PolyBound.shift (527 / 2 ^ 15) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

#print axioms negc
#print axioms pos_0

end Library.Numerics.Float64.Lgamma.LgammaAccSmallG
