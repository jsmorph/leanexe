import Library.Numerics.Float64.Lgamma.LgammaSmallFactBase

/-!
The kernel checks `pos_1` and `pos_2` and `pos_3` of `LgammaSmallFact`.  Each module holds checks
of at most 62,000 coefficient operations in the Python model, since modules of divided-difference
checks with more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaSmallFactC

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaSmallFactBase

theorem pos_1 : ddPieceOk cfg_pos
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (197 / 2 ^ 14) (65 / 4096) (67 / 2 ^ 13)
    (PolyBound.shift (197 / 2 ^ 14) smallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

theorem pos_2 : ddPieceOk cfg_pos
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (323 / 2 ^ 14) (193 / 2 ^ 13) (65 / 4096)
    (PolyBound.shift (323 / 2 ^ 14) smallList) (1 / 2 ^ 71) 0 = true := by
  decide +kernel

theorem pos_3 : ddPieceOk cfg_pos
    ⟨(1), 16, log2Lo, log2Hi,
      ⟨4,
        (307403352936852156845359246813 / 5070602400912917605986812821504),
        (1229613411747408627381436987255 / 20282409603651670423947251286016)⟩⟩
    (449 / 2 ^ 14) (1 / 32) (193 / 2 ^ 13)
    (PolyBound.shift (449 / 2 ^ 14) smallList) (1 / 2 ^ 71) 1 = true := by
  decide +kernel

#print axioms pos_1
#print axioms pos_2
#print axioms pos_3

end Library.Numerics.Float64.Lgamma.LgammaSmallFactC
