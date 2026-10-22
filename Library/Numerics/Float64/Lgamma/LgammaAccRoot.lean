import Library.Numerics.Float64.Lgamma.LgammaRootRanges
import Library.Numerics.Float64.Lgamma.LgammaRootSel
import Library.Numerics.Float64.Lgamma.LgammaAccFinal

/-!
**The step about the negative zeros** of `Lgamma.accurate`: when `rootRange` selects a range, the
code's `mulDD` is within `|log |Γ sx||/2^55` of `log |Γ sx|` (`root_leaf`).  `rootRange_spec`
names the range, and its theorem of `LgammaRootRanges` applies, with `|log |Γ sx||` bounded by
the range's bound on `|fh|`, at least `1/32`, through `|log |Γ sx|| ≤ |fh| + 2^-46`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccRoot
open CodeLib.IEEE64 LeanExe.ProofKit Tgamma

set_option exponentiation.threshold 4096

local notation "tab" => Lgamma.accurateTable

set_option maxHeartbeats 4000000 in
/-- **A selected range**: the code's product within `|log |Γ sx||/2^55`. -/
theorem root_leaf (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (sx : Float) (hsx : Finite sx.toBits) (fh : Float)
    (hfh : Finite fh.toBits)
    (hLf : |GammaBasic.lgamma (value sx.toBits)| ≤ |value fh.toBits| + 1 / 2 ^ 46)
    (o n k : UInt64) (sc : Float) (hr : Lgamma.rootRange fh.abs sx = (o, n, k, sc))
    (ho : ¬ (o == 0) = true)
    (zh zl : Float) (hT : fastTwoSum (entry tab o + sx) (entry tab (o + 1)) = (zh, zl))
    (gh gl : Float)
    (hD : Lgamma.polyDD tab (o + 3) (n - k) (zh * sc) ((zl + entry tab (o + 2)) * sc)
      ((zh * sc) * Lgamma.polyD tab (o + 3 + 2 * (n - k)) k (zh * sc)) = (gh, gl)) :
    Finite (mulDD zh (zl + entry tab (o + 2)) gh gl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab (o + 2)) gh gl).2.toBits ∧
      |value (mulDD zh (zl + entry tab (o + 2)) gh gl).1.toBits +
          value (mulDD zh (zl + entry tab (o + 2)) gh gl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 55 := by
  obtain ⟨haf, hafv⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.abs_float fh hfh
  rcases LgammaRootSel.rootRange_spec fh.abs sx haf hsx _ hr with
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨hb, hlo, hhi, he⟩ |
      ⟨he, -⟩
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range0 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB7400000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FB7400000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range1 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB1680000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FB1680000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range2 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB2D40000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FB2D40000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range3 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FAEF00000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FAEF00000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range4 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC0000000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC0000000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range5 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB0800000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FB0800000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range6 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FB1000000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FB1000000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range7 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC1300000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC1300000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range8 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC1500000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC1500000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range9 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC3400000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC3400000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range10 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC1450000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC1450000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range11 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC76B0000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range12 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC76C0000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC76C0000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range13 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC9900000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range14 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC9900000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC9900000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range15 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC76B0000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    rw [hafv] at hb
    exact LgammaRootRanges.range16 hF hRF hRM sx hsx (by push_cast at hlo ⊢; linarith)
      (by push_cast at hhi ⊢; linarith)
      (by
        have hB : (1 / 32 : ℝ) ≤ ((PolyBound.ratOfWord 0x3FC76B0000000000 : ℚ) : ℝ) := by
          have h : (1 / 32 : ℚ) ≤ PolyBound.ratOfWord 0x3FC76B0000000000 := by decide +kernel
          exact le_trans (by norm_num) ((Rat.cast_le (K := ℝ)).mpr h)
        linarith) zh zl hT gh gl hD
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -, -, -⟩ := he
    exact absurd (by decide) ho

end Library.Numerics.Float64.Lgamma.LgammaAccRoot
