import LeanExe.ProofKit.GammaDDCover
import LeanExe.ProofKit.GammaDD
import Verified.Examples.LgammaData

/-!
The definitions of the checks of `LgammaSmallFact`: the polynomial, and the Taylor-model parameters
with the lemmas that turn a kernel check of the divided difference into a bound.
-/

namespace Verified.Examples.LgammaSmallFactBase

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD
  GammaConvex GammaDDCover GammaThresholds LgammaData

/-- The polynomial below `2 ^ -5`, `LgammaApprox.smallPoly`. -/
def smallList : List ℚ :=
  ddCoeffs mainTable 381 4 ++ coeffs mainTable 389 1 8

def cfg_neg : Cfg := ⟨63 / 2 ^ 14, 12, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_neg_pi : ((cfg_neg.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_neg.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_neg (n : ℕ) (ly : LogData) (s0 R τ : ℚ) (depth : ℕ)
    (h : ddPieceOk cfg_neg ⟨(1), n, log2Lo, log2Hi, ly⟩ s0 R τ
      (PolyBound.shift s0 smallList) (1 / 2 ^ 71) depth = true)
    (t : ℝ) (ht : |t| ≤ ((63 : ℝ) / 2 ^ 14)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t) -
      eval smallList (s0 + t)| ≤ ((1 : ℝ) / 2 ^ 71) := by
  have hb := ddPieceOk_sound cfg_neg _ s0 R τ _ _ depth cfg_neg_pi h
    (t := t) (by simp only [cfg_neg]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_negc : Cfg := ⟨1 / 4096, 7, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_negc_pi : ((cfg_negc.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_negc.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_negc (n : ℕ) (ly : LogData) (s0 R τ : ℚ) (depth : ℕ)
    (h : ddPieceOk cfg_negc ⟨(1), n, log2Lo, log2Hi, ly⟩ s0 R τ
      (PolyBound.shift s0 smallList) (1 / 2 ^ 71) depth = true)
    (t : ℝ) (ht : |t| ≤ ((1 : ℝ) / 4096)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t) -
      eval smallList (s0 + t)| ≤ ((1 : ℝ) / 2 ^ 71) := by
  have hb := ddPieceOk_sound cfg_negc _ s0 R τ _ _ depth cfg_negc_pi h
    (t := t) (by simp only [cfg_negc]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_pos : Cfg := ⟨63 / 2 ^ 14, 12, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_pos_pi : ((cfg_pos.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_pos.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_pos (n : ℕ) (ly : LogData) (s0 R τ : ℚ) (depth : ℕ)
    (h : ddPieceOk cfg_pos ⟨(1), n, log2Lo, log2Hi, ly⟩ s0 R τ
      (PolyBound.shift s0 smallList) (1 / 2 ^ 71) depth = true)
    (t : ℝ) (ht : |t| ≤ ((63 : ℝ) / 2 ^ 14)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t) -
      eval smallList (s0 + t)| ≤ ((1 : ℝ) / 2 ^ 71) := by
  have hb := ddPieceOk_sound cfg_pos _ s0 R τ _ _ depth cfg_pos_pi h
    (t := t) (by simp only [cfg_pos]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_posc : Cfg := ⟨1 / 4096, 7, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_posc_pi : ((cfg_posc.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_posc.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_posc (n : ℕ) (ly : LogData) (s0 R τ : ℚ) (depth : ℕ)
    (h : ddPieceOk cfg_posc ⟨(1), n, log2Lo, log2Hi, ly⟩ s0 R τ
      (PolyBound.shift s0 smallList) (1 / 2 ^ 71) depth = true)
    (t : ℝ) (ht : |t| ≤ ((1 : ℝ) / 4096)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t) -
      eval smallList (s0 + t)| ≤ ((1 : ℝ) / 2 ^ 71) := by
  have hb := ddPieceOk_sound cfg_posc _ s0 R τ _ _ depth cfg_posc_pi h
    (t := t) (by simp only [cfg_posc]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

#print axioms piece_neg
#print axioms piece_negc
#print axioms piece_pos
#print axioms piece_posc

end Verified.Examples.LgammaSmallFactBase
