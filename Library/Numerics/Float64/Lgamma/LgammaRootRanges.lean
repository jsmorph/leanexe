import Library.Numerics.Float64.Lgamma.LgammaRootKern
import Library.Numerics.Float64.Lgamma.LgammaRootDom

/-!
**The 17 polynomials about the negative zeros** of `Lgamma.accurate`, each within
`|log |Γ sx||/2^55` on its range of `sx` (`range0` to `range16`).  Each theorem applies
`LgammaRootSpec.root_spec` with the kernel checks of `LgammaRootKern`, the bound on the shifted
argument of `LgammaRootDom`, and the entries of `RootFact` and `RootMinFact` for its row of
`LgammaApprox.rootRanges`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaRootRanges
open CodeLib.IEEE64 LeanExe.ProofKit Tgamma

set_option exponentiation.threshold 4096

local notation "tab" => Lgamma.accurateTable

set_option maxHeartbeats 4000000 in
/-- **Range 0** from `(PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ)` to `(-2 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range0 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-2 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FB7400000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (128 : UInt64) + sx) (entry tab ((128 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((128 : UInt64) + 3) ((26 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x4020000000000000)
      ((zl + entry tab ((128 : UInt64) + 2)) * Float.ofBits 0x4020000000000000)
      ((zh * Float.ofBits 0x4020000000000000) * Lgamma.polyD tab ((128 : UInt64) + 3 + 2 * ((26 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x4020000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((128 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((128 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((128 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((128 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom0 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FB7400000000000, PolyBound.ratOfWord 0xC004E147AE147AE1, (-2 : ℚ), 128, 26, 6, 3) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FB7400000000000, PolyBound.ratOfWord 0xC004E147AE147AE1, (-2 : ℚ), 128, 26, 6, 3) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num0
  exact LgammaRootSpec.root_spec hF 128 20 6 3 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (128 : UInt64) (26 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4020000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4020000000000000 = 2 ^ 3 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (437951 / 2 ^ 20 : ℚ) (695117 / 2 ^ 20 : ℚ) (764289224164770471 / 2 ^ 60 : ℚ) (679 / 2 ^ 60 : ℚ) LgammaRootKern.C0 LgammaRootKern.Cl0 LgammaRootKern.E0
    LgammaRootKern.L0 LgammaRootKern.K0 LgammaRootKern.rok0
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (764289224164770471 / 2 ^ 60 : ℚ) (764289224164770471 / 2 ^ 60 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok0 LgammaRootKern.tl0 n1 n2 n3 n4
    (1167087 / 2 ^ 20 : ℚ) (465145 / 2 ^ 18 : ℚ) (1167087 / 2 ^ 20 : ℚ) (465145 / 2 ^ 18 : ℚ) LgammaRootKern.rp0 LgammaRootKern.rn0 ⟨n24.1, Or.inl n24.2⟩ (186869 / 2 ^ 18 : ℚ) LgammaRootKern.lp0
    (-46852683983129509919 / 2 ^ 64 : ℚ) (-44361043621697138841 / 2 ^ 64 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 1** from `(-3 : ℚ)` to `(PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range1 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-3 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((PolyBound.ratOfWord 0xC004E147AE147AE1 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FB1680000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (183 : UInt64) + sx) (entry tab ((183 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((183 : UInt64) + 3) ((27 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x4030000000000000)
      ((zl + entry tab ((183 : UInt64) + 2)) * Float.ofBits 0x4030000000000000)
      ((zh * Float.ofBits 0x4030000000000000) * Lgamma.polyD tab ((183 : UInt64) + 3 + 2 * ((27 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x4030000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((183 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((183 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((183 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((183 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom1 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FB1680000000000, (-3 : ℚ), PolyBound.ratOfWord 0xC004E147AE147AE1, 183, 27, 6, 4) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FB1680000000000, (-3 : ℚ), PolyBound.ratOfWord 0xC004E147AE147AE1, 183, 27, 6, 4) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num1
  exact LgammaRootSpec.root_spec hF 183 21 6 4 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (183 : UInt64) (27 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4030000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4030000000000000 = 2 ^ 4 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (384727 / 2 ^ 19 : ℚ) (260515 / 2 ^ 19 : ℚ) (52876476252422191 / 2 ^ 56 : ℚ) (47 / 2 ^ 56 : ℚ) LgammaRootKern.C1 LgammaRootKern.Cl1 LgammaRootKern.E1
    LgammaRootKern.L1 LgammaRootKern.K1 LgammaRootKern.rok1
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (52876476252422191 / 2 ^ 56 : ℚ) (52876476252422191 / 2 ^ 56 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok1 LgammaRootKern.tl1 n1 n2 n3 n4
    (-1170827 / 2 ^ 19 : ℚ) (-773431 / 2 ^ 19 : ℚ) (773431 / 2 ^ 19 : ℚ) (1170827 / 2 ^ 19 : ℚ) LgammaRootKern.rp1 LgammaRootKern.rn1 ⟨n24.1, Or.inr n24.2⟩ (857037 / 2 ^ 20 : ℚ) LgammaRootKern.lp1
    (-25629338539291882257 / 2 ^ 63 : ℚ) (-49839775541959449833 / 2 ^ 64 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 2** from `(-7 / 2 : ℚ)` to `(-3 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range2 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-7 / 2 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-3 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FB2D40000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (240 : UInt64) + sx) (entry tab ((240 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((240 : UInt64) + 3) ((20 : UInt64) - (7 : UInt64))
      (zh * Float.ofBits 0x4050000000000000)
      ((zl + entry tab ((240 : UInt64) + 2)) * Float.ofBits 0x4050000000000000)
      ((zh * Float.ofBits 0x4050000000000000) * Lgamma.polyD tab ((240 : UInt64) + 3 + 2 * ((20 : UInt64) - (7 : UInt64)))
        (7 : UInt64) (zh * Float.ofBits 0x4050000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((240 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((240 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((240 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((240 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom2 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FB2D40000000000, (-7 / 2 : ℚ), (-3 : ℚ), 240, 20, 7, 6) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FB2D40000000000, (-7 / 2 : ℚ), (-3 : ℚ), 240, 20, 7, 6) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num2
  exact LgammaRootSpec.root_spec hF 240 13 7 6 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (240 : UInt64) (20 : UInt64) (7 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4050000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4050000000000000 = 2 ^ 6 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (626683 / 2 ^ 20 : ℚ) (668109 / 2 ^ 20 : ℚ) (734593614121796237 / 2 ^ 60 : ℚ) (653 / 2 ^ 60 : ℚ) LgammaRootKern.C2 LgammaRootKern.Cl2 LgammaRootKern.E2
    LgammaRootKern.L2 LgammaRootKern.K2 LgammaRootKern.rok2
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (734593614121796237 / 2 ^ 60 : ℚ) (734593614121796237 / 2 ^ 60 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok2 LgammaRootKern.tl2 n1 n2 n3 n4
    (3945119 / 2 ^ 19 : ℚ) (8423633 / 2 ^ 20 : ℚ) (3945119 / 2 ^ 19 : ℚ) (8423633 / 2 ^ 20 : ℚ) LgammaRootKern.rp2 LgammaRootKern.rn2 ⟨n24.1, Or.inl n24.2⟩ (488693 / 2 ^ 20 : ℚ) LgammaRootKern.lp2
    (-58172480345658311775 / 2 ^ 64 : ℚ) (-7227071362634278469 / 2 ^ 61 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 3** from `(-4 : ℚ)` to `(-7 / 2 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range3 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-4 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-7 / 2 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FAEF00000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (283 : UInt64) + sx) (entry tab ((283 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((283 : UInt64) + 3) ((20 : UInt64) - (7 : UInt64))
      (zh * Float.ofBits 0x4070000000000000)
      ((zl + entry tab ((283 : UInt64) + 2)) * Float.ofBits 0x4070000000000000)
      ((zh * Float.ofBits 0x4070000000000000) * Lgamma.polyD tab ((283 : UInt64) + 3 + 2 * ((20 : UInt64) - (7 : UInt64)))
        (7 : UInt64) (zh * Float.ofBits 0x4070000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((283 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((283 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((283 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((283 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom3 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FAEF00000000000, (-4 : ℚ), (-7 / 2 : ℚ), 283, 20, 7, 8) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FAEF00000000000, (-4 : ℚ), (-7 / 2 : ℚ), 283, 20, 7, 8) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num3
  exact LgammaRootSpec.root_spec hF 283 13 7 8 1 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (283 : UInt64) (20 : UInt64) (7 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4070000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4070000000000000 = 2 ^ 8 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (206989 / 2 ^ 18 : ℚ) (385123 / 2 ^ 19 : ℚ) (910347249286906665 / 2 ^ 60 : ℚ) (809 / 2 ^ 60 : ℚ) LgammaRootKern.C3 LgammaRootKern.Cl3 LgammaRootKern.E3
    LgammaRootKern.L3 LgammaRootKern.K3 LgammaRootKern.rok3
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (910347249286906665 / 2 ^ 60 : ℚ) (910347249286906665 / 2 ^ 60 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok3 LgammaRootKern.tl3 n1 n2 n3 n4
    (-22522997 / 2 ^ 20 : ℚ) (-2614713 / 2 ^ 17 : ℚ) (2614713 / 2 ^ 17 : ℚ) (22522997 / 2 ^ 20 : ℚ) LgammaRootKern.rp3 LgammaRootKern.rn3 ⟨n24.1, Or.inr n24.2⟩ (581671 / 2 ^ 19 : ℚ) LgammaRootKern.lp3
    (-36507616132442691657 / 2 ^ 63 : ℚ) (-36452702367154859857 / 2 ^ 63 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 4** from `(-9 / 2 : ℚ)` to `(-4 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range4 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-9 / 2 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-4 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC0000000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (326 : UInt64) + sx) (entry tab ((326 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((326 : UInt64) + 3) ((24 : UInt64) - (7 : UInt64))
      (zh * Float.ofBits 0x4060000000000000)
      ((zl + entry tab ((326 : UInt64) + 2)) * Float.ofBits 0x4060000000000000)
      ((zh * Float.ofBits 0x4060000000000000) * Lgamma.polyD tab ((326 : UInt64) + 3 + 2 * ((24 : UInt64) - (7 : UInt64)))
        (7 : UInt64) (zh * Float.ofBits 0x4060000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((326 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((326 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((326 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((326 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom4 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC0000000000000, (-9 / 2 : ℚ), (-4 : ℚ), 326, 24, 7, 7) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC0000000000000, (-9 / 2 : ℚ), (-4 : ℚ), 326, 24, 7, 7) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num4
  exact LgammaRootSpec.root_spec hF 326 17 7 7 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (326 : UInt64) (24 : UInt64) (7 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4060000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4060000000000000 = 2 ^ 7 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (603229 / 2 ^ 20 : ℚ) (676873 / 2 ^ 20 : ℚ) (372114867013812555 / 2 ^ 59 : ℚ) (331 / 2 ^ 59 : ℚ) LgammaRootKern.C4 LgammaRootKern.Cl4 LgammaRootKern.E4
    LgammaRootKern.L4 LgammaRootKern.K4 LgammaRootKern.rok4
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (372114867013812555 / 2 ^ 59 : ℚ) (372114867013812555 / 2 ^ 59 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok4 LgammaRootKern.tl4 n1 n2 n3 n4
    (13188585 / 2 ^ 19 : ℚ) (14873333 / 2 ^ 19 : ℚ) (13188585 / 2 ^ 19 : ℚ) (14873333 / 2 ^ 19 : ℚ) LgammaRootKern.rp4 LgammaRootKern.rn4 ⟨n24.1, Or.inl n24.2⟩ (888447 / 2 ^ 18 : ℚ) LgammaRootKern.lp4
    (-37303051333288377175 / 2 ^ 63 : ℚ) (-74430167010437261973 / 2 ^ 64 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 5** from `(-5 : ℚ)` to `(-9 / 2 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range5 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-5 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-9 / 2 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FB0800000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (377 : UInt64) + sx) (entry tab ((377 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((377 : UInt64) + 3) ((19 : UInt64) - (7 : UInt64))
      (zh * Float.ofBits 0x4090000000000000)
      ((zl + entry tab ((377 : UInt64) + 2)) * Float.ofBits 0x4090000000000000)
      ((zh * Float.ofBits 0x4090000000000000) * Lgamma.polyD tab ((377 : UInt64) + 3 + 2 * ((19 : UInt64) - (7 : UInt64)))
        (7 : UInt64) (zh * Float.ofBits 0x4090000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((377 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((377 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((377 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((377 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom5 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FB0800000000000, (-5 : ℚ), (-9 / 2 : ℚ), 377, 19, 7, 10) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FB0800000000000, (-5 : ℚ), (-9 / 2 : ℚ), 377, 19, 7, 10) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num5
  exact LgammaRootSpec.root_spec hF 377 12 7 10 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (377 : UInt64) (19 : UInt64) (7 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4090000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4090000000000000 = 2 ^ 10 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (626737 / 2 ^ 20 : ℚ) (585695 / 2 ^ 20 : ℚ) (689104619057447525 / 2 ^ 60 : ℚ) (613 / 2 ^ 60 : ℚ) LgammaRootKern.C5 LgammaRootKern.Cl5 LgammaRootKern.E5
    LgammaRootKern.L5 LgammaRootKern.K5 LgammaRootKern.rok5
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (689104619057447525 / 2 ^ 60 : ℚ) (689104619057447525 / 2 ^ 60 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok5 LgammaRootKern.tl5 n1 n2 n3 n4
    (-63189245 / 2 ^ 19 : ℚ) (-29478801 / 2 ^ 18 : ℚ) (29478801 / 2 ^ 18 : ℚ) (63189245 / 2 ^ 19 : ℚ) LgammaRootKern.rp5 LgammaRootKern.rn5 ⟨n24.1, Or.inr n24.2⟩ (8429321 / 2 ^ 20 : ℚ) LgammaRootKern.lp5
    (-92087808663733004339 / 2 ^ 64 : ℚ) (-11508372409109077137 / 2 ^ 61 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 6** from `(-11 / 2 : ℚ)` to `(-5 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range6 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-11 / 2 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-5 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FB1000000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (418 : UInt64) + sx) (entry tab ((418 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((418 : UInt64) + 3) ((19 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x4090000000000000)
      ((zl + entry tab ((418 : UInt64) + 2)) * Float.ofBits 0x4090000000000000)
      ((zh * Float.ofBits 0x4090000000000000) * Lgamma.polyD tab ((418 : UInt64) + 3 + 2 * ((19 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x4090000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((418 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((418 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((418 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((418 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom6 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FB1000000000000, (-11 / 2 : ℚ), (-5 : ℚ), 418, 19, 6, 10) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FB1000000000000, (-11 / 2 : ℚ), (-5 : ℚ), 418, 19, 6, 10) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num6
  exact LgammaRootSpec.root_spec hF 418 13 6 10 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (418 : UInt64) (19 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4090000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4090000000000000 = 2 ^ 10 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (285269 / 2 ^ 19 : ℚ) (609411 / 2 ^ 20 : ℚ) (167513620148650133 / 2 ^ 58 : ℚ) (149 / 2 ^ 58 : ℚ) LgammaRootKern.C6 LgammaRootKern.Cl6 LgammaRootKern.E6
    LgammaRootKern.L6 LgammaRootKern.K6 LgammaRootKern.rok6
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (167513620148650133 / 2 ^ 58 : ℚ) (167513620148650133 / 2 ^ 58 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok6 LgammaRootKern.tl6 n1 n2 n3 n4
    (124947845 / 2 ^ 20 : ℚ) (66833599 / 2 ^ 19 : ℚ) (124947845 / 2 ^ 20 : ℚ) (66833599 / 2 ^ 19 : ℚ) LgammaRootKern.rp6 LgammaRootKern.rn6 ⟨n24.1, Or.inl n24.2⟩ (2241845 / 2 ^ 18 : ℚ) LgammaRootKern.lp6
    (-23098947103865220853 / 2 ^ 62 : ℚ) (-92375517059216083221 / 2 ^ 64 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 7** from `(-6 : ℚ)` to `(-11 / 2 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range7 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-6 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-11 / 2 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC1300000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (459 : UInt64) + sx) (entry tab ((459 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((459 : UInt64) + 3) ((24 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x40B0000000000000)
      ((zl + entry tab ((459 : UInt64) + 2)) * Float.ofBits 0x40B0000000000000)
      ((zh * Float.ofBits 0x40B0000000000000) * Lgamma.polyD tab ((459 : UInt64) + 3 + 2 * ((24 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x40B0000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((459 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((459 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((459 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((459 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom7 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC1300000000000, (-6 : ℚ), (-11 / 2 : ℚ), 459, 24, 6, 12) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC1300000000000, (-6 : ℚ), (-11 / 2 : ℚ), 459, 24, 6, 12) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num7
  exact LgammaRootSpec.root_spec hF 459 18 6 12 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (459 : UInt64) (24 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x40B0000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x40B0000000000000 = 2 ^ 12 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (220135 / 2 ^ 18 : ℚ) (767279 / 2 ^ 20 : ℚ) (242040992180469975 / 2 ^ 58 : ℚ) (215 / 2 ^ 58 : ℚ) LgammaRootKern.C7 LgammaRootKern.Cl7 LgammaRootKern.E7
    LgammaRootKern.L7 LgammaRootKern.K7 LgammaRootKern.rok7
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (242040992180469975 / 2 ^ 58 : ℚ) (242040992180469975 / 2 ^ 58 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok7 LgammaRootKern.tl7 n1 n2 n3 n4
    (-803913787 / 2 ^ 20 : ℚ) (-695605971 / 2 ^ 20 : ℚ) (695605971 / 2 ^ 20 : ℚ) (803913787 / 2 ^ 20 : ℚ) LgammaRootKern.rp7 LgammaRootKern.rn7 ⟨n24.1, Or.inr n24.2⟩ (2661879 / 2 ^ 15 : ℚ) LgammaRootKern.lp7
    (-110658072421191901135 / 2 ^ 64 : ℚ) (-27662748773484551853 / 2 ^ 62 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 8** from `(-13 / 2 : ℚ)` to `(-6 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range8 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-13 / 2 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-6 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC1500000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (510 : UInt64) + sx) (entry tab ((510 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((510 : UInt64) + 3) ((24 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x40B0000000000000)
      ((zl + entry tab ((510 : UInt64) + 2)) * Float.ofBits 0x40B0000000000000)
      ((zh * Float.ofBits 0x40B0000000000000) * Lgamma.polyD tab ((510 : UInt64) + 3 + 2 * ((24 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x40B0000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((510 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((510 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((510 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((510 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom8 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC1500000000000, (-13 / 2 : ℚ), (-6 : ℚ), 510, 24, 6, 12) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC1500000000000, (-13 / 2 : ℚ), (-6 : ℚ), 510, 24, 6, 12) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num8
  exact LgammaRootSpec.root_spec hF 510 18 6 12 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (510 : UInt64) (24 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x40B0000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x40B0000000000000 = 2 ^ 12 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (764999 / 2 ^ 20 : ℚ) (438769 / 2 ^ 19 : ℚ) (964863234815296345 / 2 ^ 60 : ℚ) (857 / 2 ^ 60 : ℚ) LgammaRootKern.C8 LgammaRootKern.Cl8 LgammaRootKern.E8
    LgammaRootKern.L8 LgammaRootKern.K8 LgammaRootKern.rok8
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (964863234815296345 / 2 ^ 60 : ℚ) (964863234815296345 / 2 ^ 60 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok8 LgammaRootKern.tl8 n1 n2 n3 n4
    (703072271 / 2 ^ 20 : ℚ) (812174517 / 2 ^ 20 : ℚ) (703072271 / 2 ^ 20 : ℚ) (812174517 / 2 ^ 20 : ℚ) LgammaRootKern.rp8 LgammaRootKern.rn8 ⟨n24.1, Or.inl n24.2⟩ (10774549 / 2 ^ 17 : ℚ) LgammaRootKern.lp8
    (-3459680862797579773 / 2 ^ 59 : ℚ) (-110702732972081069923 / 2 ^ 64 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 9** from `(-7 : ℚ)` to `(-13 / 2 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range9 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-7 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-13 / 2 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC3400000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (561 : UInt64) + sx) (entry tab ((561 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((561 : UInt64) + 3) ((25 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x40D0000000000000)
      ((zl + entry tab ((561 : UInt64) + 2)) * Float.ofBits 0x40D0000000000000)
      ((zh * Float.ofBits 0x40D0000000000000) * Lgamma.polyD tab ((561 : UInt64) + 3 + 2 * ((25 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x40D0000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((561 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((561 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((561 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((561 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom9 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC3400000000000, (-7 : ℚ), (-13 / 2 : ℚ), 561, 25, 6, 14) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC3400000000000, (-7 : ℚ), (-13 / 2 : ℚ), 561, 25, 6, 14) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num9
  exact LgammaRootSpec.root_spec hF 561 19 6 14 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (561 : UInt64) (25 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x40D0000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x40D0000000000000 = 2 ^ 14 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (282809 / 2 ^ 19 : ℚ) (1895 / 2 ^ 12 : ℚ) (621903567879406121 / 2 ^ 60 : ℚ) (553 / 2 ^ 60 : ℚ) LgammaRootKern.C9 LgammaRootKern.Cl9 LgammaRootKern.E9
    LgammaRootKern.L9 LgammaRootKern.K9 LgammaRootKern.rok9
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (621903567879406121 / 2 ^ 60 : ℚ) (621903567879406121 / 2 ^ 60 : ℚ) (9 / 2 ^ 27 : ℚ) LgammaRootKern.tok9 LgammaRootKern.tl9 n1 n2 n3 n4
    (-5696287575 / 2 ^ 20 : ℚ) (-4842480811 / 2 ^ 20 : ℚ) (4842480811 / 2 ^ 20 : ℚ) (5696287575 / 2 ^ 20 : ℚ) LgammaRootKern.rp9 LgammaRootKern.rn9 ⟨n24.1, Or.inr n24.2⟩ (82240587 / 2 ^ 16 : ℚ) LgammaRootKern.lp9
    (-64562033938016094547 / 2 ^ 63 : ℚ) (-16140367457017414179 / 2 ^ 61 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 10** from `(-15 / 2 : ℚ)` to `(-7 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range10 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-15 / 2 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-7 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC1450000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (614 : UInt64) + sx) (entry tab ((614 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((614 : UInt64) + 3) ((24 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x40E0000000000000)
      ((zl + entry tab ((614 : UInt64) + 2)) * Float.ofBits 0x40E0000000000000)
      ((zh * Float.ofBits 0x40E0000000000000) * Lgamma.polyD tab ((614 : UInt64) + 3 + 2 * ((24 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x40E0000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((614 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((614 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((614 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((614 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom10 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC1450000000000, (-15 / 2 : ℚ), (-7 : ℚ), 614, 24, 6, 15) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC1450000000000, (-15 / 2 : ℚ), (-7 : ℚ), 614, 24, 6, 15) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num10
  exact LgammaRootSpec.root_spec hF 614 18 6 15 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (614 : UInt64) (24 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x40E0000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x40E0000000000000 = 2 ^ 15 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (875841 / 2 ^ 20 : ℚ) (1004947 / 2 ^ 20 : ℚ) (552475455899304427 / 2 ^ 59 : ℚ) (491 / 2 ^ 59 : ℚ) LgammaRootKern.C10 LgammaRootKern.Cl10 LgammaRootKern.E10
    LgammaRootKern.L10 LgammaRootKern.K10 LgammaRootKern.rok10
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (552475455899304427 / 2 ^ 59 : ℚ) (552475455899304427 / 2 ^ 59 : ℚ) (1 / 2 ^ 29 : ℚ) LgammaRootKern.tok10 LgammaRootKern.tl10 n1 n2 n3 n4
    (76550345 / 2 ^ 14 : ℚ) (176907293 / 2 ^ 15 : ℚ) (76550345 / 2 ^ 14 : ℚ) (176907293 / 2 ^ 15 : ℚ) LgammaRootKern.rp10 LgammaRootKern.rn10 ⟨n24.1, Or.inl n24.2⟩ (507467267 / 2 ^ 20 : ℚ) LgammaRootKern.lp10
    (-64565703324134954215 / 2 ^ 63 : ℚ) (-129130396908495050053 / 2 ^ 64 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 11** from `(-8 : ℚ)` to `(-15 / 2 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range11 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-8 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-15 / 2 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (665 : UInt64) + sx) (entry tab ((665 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((665 : UInt64) + 3) ((27 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x4100000000000000)
      ((zl + entry tab ((665 : UInt64) + 2)) * Float.ofBits 0x4100000000000000)
      ((zh * Float.ofBits 0x4100000000000000) * Lgamma.polyD tab ((665 : UInt64) + 3 + 2 * ((27 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x4100000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((665 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((665 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((665 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((665 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom11 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC76B0000000000, (-8 : ℚ), (-15 / 2 : ℚ), 665, 27, 6, 17) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC76B0000000000, (-8 : ℚ), (-15 / 2 : ℚ), 665, 27, 6, 17) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num11
  exact LgammaRootSpec.root_spec hF 665 21 6 17 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (665 : UInt64) (27 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4100000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4100000000000000 = 2 ^ 17 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (349705 / 2 ^ 19 : ℚ) (580335 / 2 ^ 20 : ℚ) (192252356895703211 / 2 ^ 58 : ℚ) (171 / 2 ^ 58 : ℚ) LgammaRootKern.C11 LgammaRootKern.Cl11 LgammaRootKern.E11
    LgammaRootKern.L11 LgammaRootKern.K11 LgammaRootKern.rok11
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (192252356895703211 / 2 ^ 58 : ℚ) (192252356895703211 / 2 ^ 58 : ℚ) (55 / 2 ^ 30 : ℚ) LgammaRootKern.tok11 LgammaRootKern.tl11 n1 n2 n3 n4
    (-46341548785 / 2 ^ 20 : ℚ) (-18968560309 / 2 ^ 19 : ℚ) (18968560309 / 2 ^ 19 : ℚ) (46341548785 / 2 ^ 20 : ℚ) LgammaRootKern.rp11 LgammaRootKern.rn11 ⟨n24.1, Or.inr n24.2⟩ (5268101779 / 2 ^ 19 : ℚ) LgammaRootKern.lp11
    (-73786786474037282047 / 2 ^ 63 : ℚ) (-147573401183629697185 / 2 ^ 64 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 12** from `(-17 / 2 : ℚ)` to `(-8 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range12 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-17 / 2 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-8 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC76C0000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (722 : UInt64) + sx) (entry tab ((722 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((722 : UInt64) + 3) ((27 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x4100000000000000)
      ((zl + entry tab ((722 : UInt64) + 2)) * Float.ofBits 0x4100000000000000)
      ((zh * Float.ofBits 0x4100000000000000) * Lgamma.polyD tab ((722 : UInt64) + 3 + 2 * ((27 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x4100000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((722 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((722 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((722 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((722 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom12 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC76C0000000000, (-17 / 2 : ℚ), (-8 : ℚ), 722, 27, 6, 17) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC76C0000000000, (-17 / 2 : ℚ), (-8 : ℚ), 722, 27, 6, 17) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num12
  exact LgammaRootSpec.root_spec hF 722 21 6 17 3 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (722 : UInt64) (27 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4100000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4100000000000000 = 2 ^ 17 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (580311 / 2 ^ 20 : ℚ) (699375 / 2 ^ 20 : ℚ) (768970944675840683 / 2 ^ 60 : ℚ) (683 / 2 ^ 60 : ℚ) LgammaRootKern.C12 LgammaRootKern.Cl12 LgammaRootKern.E12
    LgammaRootKern.L12 LgammaRootKern.K12 LgammaRootKern.rok12
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (768970944675840683 / 2 ^ 60 : ℚ) (768970944675840683 / 2 ^ 60 : ℚ) (7 / 2 ^ 27 : ℚ) LgammaRootKern.tok12 LgammaRootKern.tl12 n1 n2 n3 n4
    (9486348769 / 2 ^ 18 : ℚ) (23175628931 / 2 ^ 19 : ℚ) (9486348769 / 2 ^ 18 : ℚ) (23175628931 / 2 ^ 19 : ℚ) LgammaRootKern.rp12 LgammaRootKern.rn12 ⟨n24.1, Or.inl n24.2⟩ (10539084217 / 2 ^ 20 : ℚ) LgammaRootKern.lp12
    (-147574503942326973793 / 2 ^ 64 : ℚ) (-18446791523251882447 / 2 ^ 61 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 13** from `(-9 : ℚ)` to `(-17 / 2 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range13 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-9 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-17 / 2 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (779 : UInt64) + sx) (entry tab ((779 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((779 : UInt64) + 3) ((28 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x4130000000000000)
      ((zl + entry tab ((779 : UInt64) + 2)) * Float.ofBits 0x4130000000000000)
      ((zh * Float.ofBits 0x4130000000000000) * Lgamma.polyD tab ((779 : UInt64) + 3 + 2 * ((28 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x4130000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((779 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((779 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((779 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((779 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom13 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC9900000000000, (-9 : ℚ), (-17 / 2 : ℚ), 779, 28, 6, 20) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC9900000000000, (-9 : ℚ), (-17 / 2 : ℚ), 779, 28, 6, 20) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num13
  exact LgammaRootSpec.root_spec hF 779 22 6 20 3 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (779 : UInt64) (28 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4130000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4130000000000000 = 2 ^ 20 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (342287 / 2 ^ 19 : ℚ) (279205 / 2 ^ 19 : ℚ) (752697073073128093 / 2 ^ 60 : ℚ) (669 / 2 ^ 60 : ℚ) LgammaRootKern.C13 LgammaRootKern.Cl13 LgammaRootKern.E13
    LgammaRootKern.L13 LgammaRootKern.K13 LgammaRootKern.rok13
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (752697073073128093 / 2 ^ 60 : ℚ) (752697073073128093 / 2 ^ 60 : ℚ) (2007 / 2 ^ 30 : ℚ) LgammaRootKern.tok13 LgammaRootKern.tl13 n1 n2 n3 n4
    (-210286144609 / 2 ^ 19 : ℚ) (-337518107029 / 2 ^ 20 : ℚ) (337518107029 / 2 ^ 20 : ℚ) (210286144609 / 2 ^ 19 : ℚ) LgammaRootKern.rp13 LgammaRootKern.rn13 ⟨n24.1, Or.inr n24.2⟩ (114853250817 / 2 ^ 20 : ℚ) LgammaRootKern.lp13
    (-166020655197343035241 / 2 ^ 64 : ℚ) (-83010317171775948795 / 2 ^ 63 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 14** from `(-19 / 2 : ℚ)` to `(-9 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range14 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-19 / 2 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-9 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (838 : UInt64) + sx) (entry tab ((838 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((838 : UInt64) + 3) ((28 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x4130000000000000)
      ((zl + entry tab ((838 : UInt64) + 2)) * Float.ofBits 0x4130000000000000)
      ((zh * Float.ofBits 0x4130000000000000) * Lgamma.polyD tab ((838 : UInt64) + 3 + 2 * ((28 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x4130000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((838 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((838 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((838 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((838 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom14 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC9900000000000, (-19 / 2 : ℚ), (-9 : ℚ), 838, 28, 6, 20) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC9900000000000, (-19 / 2 : ℚ), (-9 : ℚ), 838, 28, 6, 20) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num14
  exact LgammaRootSpec.root_spec hF 838 22 6 20 3 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (838 : UInt64) (28 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4130000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4130000000000000 = 2 ^ 20 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (558397 / 2 ^ 20 : ℚ) (684555 / 2 ^ 20 : ℚ) (752676182352200349 / 2 ^ 60 : ℚ) (669 / 2 ^ 60 : ℚ) LgammaRootKern.C14 LgammaRootKern.Cl14 LgammaRootKern.E14
    LgammaRootKern.L14 LgammaRootKern.K14 LgammaRootKern.rok14
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (752676182352200349 / 2 ^ 60 : ℚ) (752676182352200349 / 2 ^ 60 : ℚ) (251 / 2 ^ 27 : ℚ) LgammaRootKern.tok14 LgammaRootKern.tl14 n1 n2 n3 n4
    (337527677679 / 2 ^ 20 : ℚ) (420581732105 / 2 ^ 20 : ℚ) (337527677679 / 2 ^ 20 : ℚ) (420581732105 / 2 ^ 20 : ℚ) LgammaRootKern.rp14 LgammaRootKern.rn14 ⟨n24.1, Or.inl n24.2⟩ (57428536231 / 2 ^ 19 : ℚ) LgammaRootKern.lp14
    (-166020758982271881795 / 2 ^ 64 : ℚ) (-83010369064504561761 / 2 ^ 63 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 15** from `(-10 : ℚ)` to `(-19 / 2 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range15 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-10 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-19 / 2 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (897 : UInt64) + sx) (entry tab ((897 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((897 : UInt64) + 3) ((27 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x4170000000000000)
      ((zl + entry tab ((897 : UInt64) + 2)) * Float.ofBits 0x4170000000000000)
      ((zh * Float.ofBits 0x4170000000000000) * Lgamma.polyD tab ((897 : UInt64) + 3 + 2 * ((27 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x4170000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((897 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((897 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((897 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((897 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom15 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC76B0000000000, (-10 : ℚ), (-19 / 2 : ℚ), 897, 27, 6, 24) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC76B0000000000, (-10 : ℚ), (-19 / 2 : ℚ), 897, 27, 6, 24) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num15
  exact LgammaRootSpec.root_spec hF 897 21 6 24 3 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (897 : UInt64) (27 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4170000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4170000000000000 = 2 ^ 24 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (497301 / 2 ^ 19 : ℚ) (412643 / 2 ^ 19 : ℚ) (273394116002316531 / 2 ^ 58 : ℚ) (243 / 2 ^ 58 : ℚ) LgammaRootKern.C15 LgammaRootKern.Cl15 LgammaRootKern.E15
    LgammaRootKern.L15 LgammaRootKern.K15 LgammaRootKern.rok15
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (273394116002316531 / 2 ^ 58 : ℚ) (273394116002316531 / 2 ^ 58 : ℚ) (1 / 2 ^ 28 : ℚ) LgammaRootKern.tok15 LgammaRootKern.tl15 n1 n2 n3 n4
    (-4171139599115 / 2 ^ 20 : ℚ) (-853685985271 / 2 ^ 18 : ℚ) (853685985271 / 2 ^ 18 : ℚ) (4171139599115 / 2 ^ 20 : ℚ) LgammaRootKern.rp15 LgammaRootKern.rn15 ⟨n24.1, Or.inr n24.2⟩ (567648603245 / 2 ^ 20 : ℚ) LgammaRootKern.lp15
    (-184467436519039061843 / 2 ^ 64 : ℚ) (-184467434610748909899 / 2 ^ 64 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

set_option maxHeartbeats 4000000 in
/-- **Range 16** from `(-21 / 2 : ℚ)` to `(-10 : ℚ)`: the polynomial about the zero of `log |Γ|` between these ends, within
`|log |Γ x||/2^55`. -/
theorem range16 (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits)
    (hlo : ((-21 / 2 : ℚ) : ℝ) < value sx.toBits) (hhi : value sx.toBits < ((-10 : ℚ) : ℝ))
    (hL : |GammaBasic.lgamma (value sx.toBits)| ≤
      (1 + 1 / 2 ^ 40) * ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ))
    (zh zl : Float)
    (hT : fastTwoSum (entry tab (954 : UInt64) + sx) (entry tab ((954 : UInt64) + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab ((954 : UInt64) + 3) ((27 : UInt64) - (6 : UInt64))
      (zh * Float.ofBits 0x4170000000000000)
      ((zl + entry tab ((954 : UInt64) + 2)) * Float.ofBits 0x4170000000000000)
      ((zh * Float.ofBits 0x4170000000000000) * Lgamma.polyD tab ((954 : UInt64) + 3 + 2 * ((27 : UInt64) - (6 : UInt64)))
        (6 : UInt64) (zh * Float.ofBits 0x4170000000000000)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab ((954 : UInt64) + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab ((954 : UInt64) + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab ((954 : UInt64) + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab ((954 : UInt64) + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  have hdom := LgammaRootDom.dom16 (value sx.toBits) hlo hhi hL
  have hrf := hRF _ _ _ _ _ _ _ (by decide +kernel : (0x3FC76B0000000000, (-21 / 2 : ℚ), (-10 : ℚ), 954, 27, 6, 24) ∈
    LgammaApprox.rootRanges) (value sx.toBits) hlo hhi hL
  have hrm := hRM _ _ _ _ _ _ _ (by decide +kernel : (0x3FC76B0000000000, (-21 / 2 : ℚ), (-10 : ℚ), 954, 27, 6, 24) ∈
    LgammaApprox.rootRanges) sx.toBits hsx hlo hhi
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18, n19,
    n20, n21, n22, n23, n24⟩ := LgammaRootKern.num16
  exact LgammaRootSpec.root_spec hF 954 21 6 24 3 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (954 : UInt64) (27 : UInt64) (6 : UInt64) rfl
    (by decide) rfl (by decide) (by decide) (by decide) (by decide) (Float.ofBits 0x4170000000000000)
    (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide))
    (by rw [F64Bits.toBits_ofBits]; decide +kernel)
    (by rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
          show PolyBound.ratOfWord 0x4170000000000000 = 2 ^ 24 by decide +kernel]; push_cast; ring)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (206321 / 2 ^ 18 : ℚ) (994599 / 2 ^ 20 : ℚ) (273393291368595699 / 2 ^ 58 : ℚ) (243 / 2 ^ 58 : ℚ) LgammaRootKern.C16 LgammaRootKern.Cl16 LgammaRootKern.E16
    LgammaRootKern.L16 LgammaRootKern.K16 LgammaRootKern.rok16
    (fun m => LgammaPolyIv.pz_nonneg _ m) (fun m => LgammaPolyIv.pz_nonneg _ m)
    (273393291368595699 / 2 ^ 58 : ℚ) (273393291368595699 / 2 ^ 58 : ℚ) (1 / 2 ^ 28 : ℚ) LgammaRootKern.tok16 LgammaRootKern.tl16 n1 n2 n3 n4
    (1707376985267 / 2 ^ 19 : ℚ) (4171149470241 / 2 ^ 20 : ℚ) (1707376985267 / 2 ^ 19 : ℚ) (4171149470241 / 2 ^ 20 : ℚ) LgammaRootKern.rp16 LgammaRootKern.rn16 ⟨n24.1, Or.inl n24.2⟩ (141912585019 / 2 ^ 18 : ℚ) LgammaRootKern.lp16
    (-46116861715858138147 / 2 ^ 62 : ℚ) (-92233722477573716961 / 2 ^ 63 : ℚ) n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 n16 n17 n18 n19 n20 n21 n22 n23
    sx hsx (by have := hdom.1; push_cast at this ⊢; linarith)
    (by have := hdom.2; push_cast at this ⊢; linarith) hrf hrm zh zl hT fh fl hD

end Library.Numerics.Float64.Lgamma.LgammaRootRanges
