import Library.Numerics.Float64.Lgamma.LgammaAccSmallBase

/-!
The kernel checks `pos_1` and `pos_2` of `LgammaAccSmall`.  Each module holds checks of at most
62,000 coefficient operations in the Python model, since modules of divided-difference checks with
more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccSmallH

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaAccSmallBase

theorem pos_1 : ddPieceOk cfg_pos
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (1549 / 2 ^ 15) (515 / 2 ^ 13) (519 / 2 ^ 14)
    (PolyBound.shift (1549 / 2 ^ 15) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

theorem pos_2 : ddPieceOk cfg_pos
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (2571 / 2 ^ 15) (1541 / 2 ^ 14) (515 / 2 ^ 13)
    (PolyBound.shift (2571 / 2 ^ 15) accSmallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

#print axioms pos_1
#print axioms pos_2

end Library.Numerics.Float64.Lgamma.LgammaAccSmallH
