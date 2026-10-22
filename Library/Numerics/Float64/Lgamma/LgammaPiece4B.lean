import Library.Numerics.Float64.Lgamma.LgammaPiece4Base

/-!
The kernel checks `nege_2` and `neg_0` of piece 4 of `cr_lgamma`'s piecewise polynomial
(`LgammaPiece4`).  Each module holds checks of at most 62,000 coefficient operations in the Python
model, since modules with more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece4B

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece4Base

theorem nege_2 : ddRelOk cfg_nege
    ⟨1, 16, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (-2568390443008019 / 27021597764222976) (675718614745093 / 6755399441055744)
        (405651071172611 / 2 ^ 52)
    (PolyBound.shift (-2568390443008019 / 27021597764222976) q4) (-1) εin4 εout
        (716317418111 / 2 ^ 40) 1 = true := by
  decide +kernel

theorem neg_0 : ddRelOk cfg_neg
    ⟨1, 16, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (-676818126372869 / 2 ^ 53) (405651071172611 / 2 ^ 52) (135583527600129 / 2 ^ 51)
    (PolyBound.shift (-676818126372869 / 2 ^ 53) q4) (-1) εin4 εout (687316471523 / 2 ^ 40) 3 =
        true := by
  decide +kernel

#print axioms nege_2
#print axioms neg_0

end Library.Numerics.Float64.Lgamma.LgammaPiece4B
