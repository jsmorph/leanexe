import Verified.Examples.LgammaPiece4Base

/-!
The kernel checks `neg_1` and `neg_2` of piece 4 of `cr_lgamma`'s piecewise polynomial
(`LgammaPiece4`).  Each module holds checks of at most 62,000 coefficient operations in the Python
model, since modules with more stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaPiece4C

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece4Base

theorem neg_1 : ddRelOk cfg_neg
    ⟨1, 16, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (-407850094428163 / 2 ^ 53) (135583527600129 / 2 ^ 51) (136683039227905 / 2 ^ 52)
    (PolyBound.shift (-407850094428163 / 2 ^ 53) q4) (-1) εin4 εout (659202703727 / 2 ^ 40) 3 =
        true := by
  decide +kernel

theorem neg_2 : ddRelOk cfg_neg
    ⟨1, 16, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (-138882062483457 / 2 ^ 53) (136683039227905 / 2 ^ 52) (1 / 2048)
    (PolyBound.shift (-138882062483457 / 2 ^ 53) q4) (-1) εin4 εout (631921513997 / 2 ^ 40) 3 =
        true := by
  decide +kernel

#print axioms neg_1
#print axioms neg_2

end Verified.Examples.LgammaPiece4C
