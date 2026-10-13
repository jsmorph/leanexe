import Verified.Examples.LgammaPiece10Base

/-!
The kernel checks `nege_0` and `nege_1` of piece 10 of `cr_lgamma`'s piecewise polynomial
(`LgammaPiece10`).  Each module holds checks of at most 62,000 coefficient operations in the Python
model, since modules with more stopped at the runner's memory limit.
-/

namespace Verified.Examples.LgammaPiece10A

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece10Base

theorem nege_0 : ddRelOk cfg_nege
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (-108015564182871 / 2 ^ 51) (64699387346945 / 2 ^ 50) (21658088417963 / 2 ^ 49)
    (PolyBound.shift (-108015564182871 / 2 ^ 51) q10) (1) εin10 εout (221005884173 / 2 ^ 39) 3 =
        true := by
  decide +kernel

theorem nege_1 : ddRelOk cfg_nege
    ⟨2, 15, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (-65249143160833 / 2 ^ 51) (21658088417963 / 2 ^ 49) (21932966324907 / 2 ^ 50)
    (PolyBound.shift (-65249143160833 / 2 ^ 51) q10) (1) εin10 εout (224424594225 / 2 ^ 39) 2 =
        true := by
  decide +kernel

#print axioms nege_0
#print axioms nege_1

end Verified.Examples.LgammaPiece10A
