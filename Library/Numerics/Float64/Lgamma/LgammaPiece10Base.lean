import LeanExe.ProofKit.GammaDDCover
import LeanExe.ProofKit.GammaRel
import Library.Numerics.Float64.Lgamma.LgammaData

/-!
The definitions of the checks of piece 10 of `cr_lgamma`'s piecewise polynomial (`LgammaPiece10`):
the polynomial `Q` of the divided difference, the inner relative bound, and the Taylor-model
parameters with the lemmas that turn a kernel check into a bound.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaPiece10Base

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaDD GammaRel
  GammaConvex GammaDDCover GammaThresholds LgammaData

/-- `Q s = pieceP 10 (2 + s - off 10)`: `lgamma (2 + s) ≈ s Q s`. -/
def q10 : List ℚ := PolyBound.shift (2 - off 10) (pieceP 10)

/-- The inner and outer relative bounds of the checks. -/
def εin10 : ℚ := 15 / 16 / 2 ^ 63

def εout : ℚ := 1 / 2 ^ 63

def cfg_nege : Cfg := ⟨21383210511019 / 2 ^ 51, 14, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_nege_pi : ((cfg_nege.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_nege.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_nege (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_nege ⟨2, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q10) σ εin10 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((21383210511019 : ℝ) / 2 ^ 51)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t) - eval q10 (s0 + t)| ≤
      εout * |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_nege _ s0 R τ _ σ _ _ m0 depth cfg_nege_pi h
    (t := t) (by simp only [cfg_nege]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_negc : Cfg := ⟨1 / 4096, 7, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_negc_pi : ((cfg_negc.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_negc.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_negc (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_negc ⟨2, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q10) σ εin10 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((1 : ℝ) / 4096)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t) - eval q10 (s0 + t)| ≤
      εout * |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_negc _ s0 R τ _ σ _ _ m0 depth cfg_negc_pi h
    (t := t) (by simp only [cfg_negc]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_posc : Cfg := ⟨1 / 4096, 7, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_posc_pi : ((cfg_posc.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_posc.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_posc (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_posc ⟨2, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q10) σ εin10 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((1 : ℝ) / 4096)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|) :
    |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t) - eval q10 (s0 + t)| ≤
      εout * |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_posc _ s0 R τ _ σ _ _ m0 depth cfg_posc_pi h
    (t := t) (by simp only [cfg_posc]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_pos : Cfg := ⟨303396489789441 / 11258999068426240, 14, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_pos_pi : ((cfg_pos.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_pos.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_pos (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_pos ⟨2, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q10) σ εin10 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((303396489789441 : ℝ) / 11258999068426240)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|)
        :
    |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t) - eval q10 (s0 + t)| ≤
      εout * |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_pos _ s0 R τ _ σ _ _ m0 depth cfg_pos_pi h
    (t := t) (by simp only [cfg_pos]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

def cfg_pose : Cfg := ⟨101132163263147 / 11258999068426240, 14, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_pose_pi : ((cfg_pose.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg_pose.piHi : ℚ) : ℝ) := pi_bounds20

theorem piece_pose (n : ℕ) (ly : LogData) (s0 R τ σ m0 : ℚ) (depth : ℕ)
    (h : ddRelOk cfg_pose ⟨2, n, log2Lo, log2Hi, ly⟩ s0 R τ (PolyBound.shift s0 q10) σ εin10 εout
      m0 depth = true)
    (t : ℝ) (ht : |t| ≤ ((101132163263147 : ℝ) / 11258999068426240)) (hτ : (τ : ℝ) ≤ |(s0 : ℝ) + t|)
        :
    |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t) - eval q10 (s0 + t)| ≤
      εout * |(lgamma ((2 : ℝ) + (s0 + t)) - lgamma (2 : ℝ)) / (s0 + t)| := by
  have hb := ddRelOk_sound cfg_pose _ s0 R τ _ σ _ _ m0 depth cfg_pose_pi h
    (t := t) (by simp only [cfg_pose]; push_cast; exact ht) hτ
  rw [eval_shift] at hb
  push_cast at hb
  exact hb

#print axioms piece_nege
#print axioms piece_negc
#print axioms piece_posc
#print axioms piece_pos
#print axioms piece_pose

end Library.Numerics.Float64.Lgamma.LgammaPiece10Base
