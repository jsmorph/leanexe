import Library.Numerics.Float64.Lgamma.LgammaPiece4Base

/-!
The kernel checks `nege_0` and `nege_1` of piece 4 of `cr_lgamma`'s piecewise polynomial
(`LgammaPiece4`).  Each module holds checks of at most 62,000 coefficient operations in the Python
model, since modules with more stopped at the runner's memory limit.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece4A

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData LgammaPiece4Base

theorem nege_0 : ddRelOk cfg_nege
    ⟨1, 16, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (-3106326506897431 / 27021597764222976) (135033771786241 / 2 ^ 50)
        (1485921245462539 / 13510798882111488)
    (PolyBound.shift (-3106326506897431 / 27021597764222976) q4) (-1) εin4 εout
        (736173735345 / 2 ^ 40) 3 = true := by
  decide +kernel

theorem nege_1 : ddRelOk cfg_nege
    ⟨1, 16, log2Lo, log2Hi,
      ⟨4, (307403352936852156845359246813 / 2 ^ 102),
        (1229613411747408627381436987255 / 2 ^ 104)⟩⟩
    (-945786158317575 / 2 ^ 53) (1485921245462539 / 13510798882111488)
        (675718614745093 / 6755399441055744)
    (PolyBound.shift (-945786158317575 / 2 ^ 53) q4) (-1) εin4 εout (726191780533 / 2 ^ 40) 2 =
        true := by
  decide +kernel

#print axioms nege_0
#print axioms nege_1

end Library.Numerics.Float64.Lgamma.LgammaPiece4A
