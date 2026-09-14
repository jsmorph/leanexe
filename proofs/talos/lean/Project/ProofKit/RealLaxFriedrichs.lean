import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Project.ProofKit.RealLaxFriedrichs

noncomputable section

variable {ι : Type*}

def waveMinus (a : ℝ) (jump fluxJump : ι → ℝ) : ι → ℝ :=
  fun i => (jump i-fluxJump i/a)/2

def wavePlus (a : ℝ) (jump fluxJump : ι → ℝ) : ι → ℝ :=
  fun i => (jump i+fluxJump i/a)/2

def fluctuationMinus (a : ℝ) (jump fluxJump : ι → ℝ) : ι → ℝ :=
  fun i => (fluxJump i-a*jump i)/2

def fluctuationPlus (a : ℝ) (jump fluxJump : ι → ℝ) : ι → ℝ :=
  fun i => (fluxJump i+a*jump i)/2

def numericalFlux (F : (ι → ℝ) → ι → ℝ) (a : ℝ) (L R : ι → ℝ) : ι → ℝ :=
  fun i => (F L i+F R i)/2-a*(R i-L i)/2

theorem wave_sum (a : ℝ) (jump fluxJump : ι → ℝ) :
    waveMinus a jump fluxJump+wavePlus a jump fluxJump = jump := by
  funext i
  simp only [Pi.add_apply, waveMinus, wavePlus]
  ring

theorem weighted_wave_sum (a : ℝ) (ha : a ≠ 0) (jump fluxJump : ι → ℝ) :
    -a • waveMinus a jump fluxJump+a • wavePlus a jump fluxJump = fluxJump := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, waveMinus, wavePlus]
  field_simp [ha]
  ring

theorem fluctuations_of_waves (a : ℝ) (ha : a ≠ 0) (jump fluxJump : ι → ℝ) :
    -a • waveMinus a jump fluxJump = fluctuationMinus a jump fluxJump ∧
    a • wavePlus a jump fluxJump = fluctuationPlus a jump fluxJump := by
  constructor <;> funext i <;>
    simp only [Pi.smul_apply, smul_eq_mul, waveMinus, wavePlus,
      fluctuationMinus, fluctuationPlus] <;> field_simp [ha] <;> ring

theorem fluctuation_sum (a : ℝ) (jump fluxJump : ι → ℝ) :
    fluctuationMinus a jump fluxJump+fluctuationPlus a jump fluxJump = fluxJump := by
  funext i
  simp only [Pi.add_apply, fluctuationMinus, fluctuationPlus]
  ring

theorem numericalFlux_left (F : (ι → ℝ) → ι → ℝ) (a : ℝ) (L R : ι → ℝ) :
    numericalFlux F a L R = F L+fluctuationMinus a (R-L) (F R-F L) := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, numericalFlux, fluctuationMinus]
  ring

theorem numericalFlux_right (F : (ι → ℝ) → ι → ℝ) (a : ℝ) (L R : ι → ℝ) :
    numericalFlux F a L R = F R-fluctuationPlus a (R-L) (F R-F L) := by
  funext i
  simp only [Pi.sub_apply, numericalFlux, fluctuationPlus]
  ring

theorem numericalFlux_consistent (F : (ι → ℝ) → ι → ℝ) (a : ℝ) (U : ι → ℝ) :
    numericalFlux F a U U = F U := by
  funext i
  simp only [numericalFlux]
  ring

theorem waves_zero (a : ℝ) :
    waveMinus (ι := ι) a 0 0 = 0 ∧ wavePlus (ι := ι) a 0 0 = 0 := by
  constructor <;> funext i <;> simp [waveMinus, wavePlus]

theorem numericalFlux_reverse (F : (ι → ℝ) → ι → ℝ) (a : ℝ) (L R : ι → ℝ) :
    numericalFlux (fun U => -F U) a R L = -numericalFlux F a L R := by
  funext i
  simp only [numericalFlux, Pi.neg_apply]
  ring

#print axioms wave_sum
#print axioms weighted_wave_sum
#print axioms fluctuation_sum
#print axioms numericalFlux_consistent
end
end Project.ProofKit.RealLaxFriedrichs
