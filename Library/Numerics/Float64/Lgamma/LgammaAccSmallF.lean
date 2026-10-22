import Library.Numerics.Float64.Lgamma.LgammaAccSmallBase

/-!
The kernel checks `neg_6` and `neg_7` of `LgammaAccSmall`.  Each module holds checks of at most
62,000 coefficient operations in the Python model, since modules of divided-difference checks with
more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccSmallF

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaAccSmallBase

theorem neg_6 : ddPieceOk cfg_neg
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (-1549 / 2 ^ 15) (515 / 2 ^ 13) (519 / 2 ^ 14)
    (PolyBound.shift (-1549 / 2 ^ 15) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

theorem neg_7 : ddPieceOk cfg_neg
    ⟨(1), 17, log2Lo, log2Hi,
      ⟨4,
        (2388923773544278907367941202429 / 20282409603651670423947251286016),
        (4665866745203669740953010161 / 39614081257132168796771975168)⟩⟩
    (-527 / 2 ^ 15) (519 / 2 ^ 14) (1 / 2048)
    (PolyBound.shift (-527 / 2 ^ 15) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

#print axioms neg_6
#print axioms neg_7

end Library.Numerics.Float64.Lgamma.LgammaAccSmallF
