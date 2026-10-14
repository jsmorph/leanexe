import Verified.Examples.LgammaSmallFactBase

/-!
The kernel checks `neg_0` and `neg_1` and `neg_2` of `LgammaSmallFact`.  Each module holds checks
of at most 62,000 coefficient operations in the Python model, since modules of divided-difference
checks with more stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaSmallFactA

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaSmallFactBase

theorem neg_0 : ddPieceOk cfg_neg
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (-449 / 2 ^ 14) (1 / 32) (193 / 2 ^ 13)
    (PolyBound.shift (-449 / 2 ^ 14) smallList) (1 / 2 ^ 71) 1 = true := by
  decide +kernel

theorem neg_1 : ddPieceOk cfg_neg
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (-323 / 2 ^ 14) (193 / 2 ^ 13) (65 / 4096)
    (PolyBound.shift (-323 / 2 ^ 14) smallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

theorem neg_2 : ddPieceOk cfg_neg
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (-197 / 2 ^ 14) (65 / 4096) (67 / 2 ^ 13)
    (PolyBound.shift (-197 / 2 ^ 14) smallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

#print axioms neg_0
#print axioms neg_1
#print axioms neg_2

end Verified.Examples.LgammaSmallFactA
