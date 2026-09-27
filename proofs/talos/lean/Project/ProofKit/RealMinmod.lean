import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Project.ProofKit.RealMinmod
noncomputable section

def minmod (a b : ℝ) : ℝ := max 0 (min a b)+min 0 (max a b)

theorem minmod_self (a : ℝ) : minmod a a = a := by
  simpa only [minmod, min_self, max_self, zero_add] using max_add_min 0 a

theorem minmod_comm (a b : ℝ) : minmod a b = minmod b a := by
  simp only [minmod, min_comm a b, max_comm a b]

theorem minmod_neg (a b : ℝ) : minmod (-a) (-b) = -minmod a b := by
  simp only [minmod, min_def, max_def]
  split_ifs <;> linarith

theorem minmod_bounds (a b : ℝ) :
    min 0 a ≤ minmod a b ∧ minmod a b ≤ max 0 a := by
  simp only [minmod, min_def, max_def]
  split_ifs <;> constructor <;> linarith

variable {ι : Type*}

def slope (L U R : ι → ℝ) : ι → ℝ :=
  fun i => minmod (U i-L i) (R i-U i)

def leftFace (L U R : ι → ℝ) : ι → ℝ := fun i => U i-slope L U R i/2

def rightFace (L U R : ι → ℝ) : ι → ℝ := fun i => U i+slope L U R i/2

theorem slope_constant (U : ι → ℝ) : slope U U U = 0 := by
  funext i
  simp [slope, minmod_self]

theorem faces_constant (U : ι → ℝ) : leftFace U U U = U ∧ rightFace U U U = U := by
  constructor <;> funext i <;> simp [leftFace, rightFace, slope_constant]

theorem slope_linear (U D : ι → ℝ) : slope (U-D) U (U+D) = D := by
  funext i
  simp only [slope, Pi.sub_apply, Pi.add_apply]
  rw [show U i-(U i-D i) = D i by ring, show U i+D i-U i = D i by ring]
  exact minmod_self _

theorem faces_linear (U D : ι → ℝ) :
    leftFace (U-D) U (U+D) = (fun i => U i-D i/2) ∧
    rightFace (U-D) U (U+D) = (fun i => U i+D i/2) := by
  constructor <;> funext i <;> simp [leftFace, rightFace, slope_linear]

theorem slope_reverse (L U R : ι → ℝ) : slope R U L = -slope L U R := by
  funext i
  simp only [slope, Pi.neg_apply]
  rw [show U i-R i = -(R i-U i) by ring, show L i-U i = -(U i-L i) by ring,
    minmod_neg, minmod_comm]

theorem faces_reflect (L U R : ι → ℝ) : leftFace L U R = rightFace R U L := by
  funext i
  change U i-slope L U R i/2 = U i+slope R U L i/2
  rw [slope_reverse L U R]
  simp only [Pi.neg_apply]
  ring

theorem face_average (L U R : ι → ℝ) :
    (fun i => (leftFace L U R i+rightFace L U R i)/2) = U := by
  funext i
  simp only [leftFace, rightFace]
  ring

theorem half_step_bounds (u d s : ℝ) (hs : min 0 d ≤ s ∧ s ≤ max 0 d) :
    min u (u+d) ≤ u+s/2 ∧ u+s/2 ≤ max u (u+d) := by
  by_cases hd : 0 ≤ d
  · have hu : u ≤ u+d := by linarith
    rw [min_eq_left hd, max_eq_right hd] at hs
    rw [min_eq_left hu, max_eq_right hu]
    constructor <;> linarith [hs.1, hs.2]
  · have hd : d ≤ 0 := le_of_not_ge hd
    have hu : u+d ≤ u := by linarith
    rw [min_eq_right hd, max_eq_left hd] at hs
    rw [min_eq_right hu, max_eq_left hu]
    constructor <;> linarith [hs.1, hs.2]

theorem rightFace_bounds (L U R : ι → ℝ) (i : ι) :
    min (U i) (R i) ≤ rightFace L U R i ∧
    rightFace L U R i ≤ max (U i) (R i) := by
  have hs := minmod_bounds (R i-U i) (U i-L i)
  rw [minmod_comm (R i-U i) (U i-L i)] at hs
  have h := half_step_bounds (U i) (R i-U i) (slope L U R i) hs
  simpa only [add_sub_cancel, rightFace] using h

theorem leftFace_bounds (L U R : ι → ℝ) (i : ι) :
    min (U i) (L i) ≤ leftFace L U R i ∧
    leftFace L U R i ≤ max (U i) (L i) := by
  rw [faces_reflect]
  exact rightFace_bounds R U L i

#print axioms minmod_bounds
#print axioms faces_constant
#print axioms faces_linear
#print axioms faces_reflect
#print axioms face_average
#print axioms leftFace_bounds
#print axioms rightFace_bounds
end
end Project.ProofKit.RealMinmod
