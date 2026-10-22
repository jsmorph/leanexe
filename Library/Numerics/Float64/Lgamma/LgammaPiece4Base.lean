import LeanExe.ProofKit.GammaDDCover
import LeanExe.ProofKit.GammaRel
import Library.Numerics.Float64.Lgamma.LgammaData

/-!
The definitions of the checks of piece 4 of `cr_lgamma`'s piecewise polynomial (`LgammaPiece4`):
the polynomial `Q` of the divided difference, the inner relative bound, and the Taylor-model
parameters with the lemmas that turn a kernel check into a bound.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece4Base

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData

/-- `Q s = -pieceP 4 (1 + s - off 4)`: `lgamma (1 + s) ≈ s Q s`. -/
def q4 : List ℚ := scaleP (-1) (PolyBound.shift (1 - off 4) (pieceP 4))

/-- The inner and outer relative bounds of the checks. -/
def εin4 : ℚ := 15 / 16 / 2 ^ 63

def εout : ℚ := 1 / 2 ^ 63

def cfg_nege : Cfg := ⟨134484015972353 / 27021597764222976, 14, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_nege_pi : ((cfg_nege.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_nege.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_nege (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_nege ⟨1, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q4) σ εin4 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((134484015972353 : ℝ) / 27021597764222976)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|)
        :
    |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t) - eval q4 (s0 + t)| ≤
      εout * |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_nege _ s0 R τ _ σ _ _ m0 depth cfg_nege_pi h
    (t := t) (by simp only [cfg_nege]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_neg : Cfg := ⟨134484015972353 / 2 ^ 53, 14, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_neg_pi : ((cfg_neg.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_neg.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_neg (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_neg ⟨1, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q4) σ εin4 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((134484015972353 : ℝ) / 2 ^ 53)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t) - eval q4 (s0 + t)| ≤
      εout * |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_neg _ s0 R τ _ σ _ _ m0 depth cfg_neg_pi h
    (t := t) (by simp only [cfg_neg]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_negc : Cfg := ⟨1 / 4096, 7, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_negc_pi : ((cfg_negc.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_negc.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_negc (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_negc ⟨1, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q4) σ εin4 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((1 : ℝ) / 4096)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t) - eval q4 (s0 + t)| ≤
      εout * |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_negc _ s0 R τ _ σ _ _ m0 depth cfg_negc_pi h
    (t := t) (by simp only [cfg_negc]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_posc : Cfg := ⟨1 / 4096, 7, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_posc_pi : ((cfg_posc.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_posc.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_posc (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_posc ⟨1, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q4) σ εin4 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((1 : ℝ) / 4096)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t) - eval q4 (s0 + t)| ≤
      εout * |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_posc _ s0 R τ _ σ _ _ m0 depth cfg_posc_pi h
    (t := t) (by simp only [cfg_posc]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_pose : Cfg := ⟨26388279066625 / 6755399441055744, 14, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_pose_pi : ((cfg_pose.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_pose.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_pose (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_pose ⟨1, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q4) σ εin4 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((26388279066625 : ℝ) / 6755399441055744)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t) - eval q4 (s0 + t)| ≤
      εout * |(lgamma ((1 : ℝ) + (s0 + t)) - lgamma (1 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_pose _ s0 R τ _ σ _ _ m0 depth cfg_pose_pi h
    (t := t) (by simp only [cfg_pose]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

#print axioms piece_nege
#print axioms piece_neg
#print axioms piece_negc
#print axioms piece_posc
#print axioms piece_pose

end Library.Numerics.Float64.Lgamma.LgammaPiece4Base
