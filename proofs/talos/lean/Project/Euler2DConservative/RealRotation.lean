import Project.Euler2DConservative.RealJacobian

namespace Project.Euler2DConservative.RealFlux
open Guard (Vec4 pressure internalEnergy Admissible)
open scoped Matrix

abbrev Direction := Fin 2 → ℝ
def UnitDirection (n : Direction) : Prop := n 0 ^ 2 + n 1 ^ 2 = 1

noncomputable section

def rotation (n : Direction) : Mat4 :=
  !![1, 0, 0, 0;
    0, n 0, n 1, 0;
    0, -n 1, n 0, 0;
    0, 0, 0, 1]

def rotate (n : Direction) (U : Vec4) : Vec4 := rotation n *ᵥ U

theorem rotate_eq (n : Direction) (U : Vec4) :
    rotate n U = ![U 0, n 0*U 1+n 1*U 2, -n 1*U 1+n 0*U 2, U 3] := by
  ext i
  fin_cases i <;> simp [rotate, rotation, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem rotation_mul_transpose (n : Direction) (hn : UnitDirection n) :
    rotation n * (rotation n).transpose = 1 := by
  change n 0 ^ 2 + n 1 ^ 2 = 1 at hn
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]
    <;> nlinarith [hn]

theorem transpose_mul_rotation (n : Direction) (hn : UnitDirection n) :
    (rotation n).transpose * rotation n = 1 := by
  change n 0 ^ 2 + n 1 ^ 2 = 1 at hn
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]
    <;> nlinarith [hn]

theorem pressure_rotate (n : Direction) (hn : UnitDirection n) (U : Vec4) :
    pressure (rotate n U) = pressure U := by
  have hnorm : (n 0*U 1+n 1*U 2)^2+(-n 1*U 1+n 0*U 2)^2 = U 1^2+U 2^2 := by
    calc
      _ = (n 0^2+n 1^2)*(U 1^2+U 2^2) := by ring
      _ = _ := by rw [hn]; ring
  simp only [neg_mul] at hnorm
  simp [pressure, internalEnergy, rotate_eq, hnorm]

theorem admissible_rotate (n : Direction) (hn : UnitDirection n) (U : Vec4)
    (hU : Admissible U) : Admissible (rotate n U) := by
  exact ⟨by simpa [rotate_eq] using hU.1, by rw [pressure_rotate n hn]; exact hU.2⟩

def directionalFlux (n : Direction) (U : Vec4) : Vec4 :=
  n 0 • xFlux U + n 1 • yFlux U

theorem rotate_directionalFlux (n : Direction) (hn : UnitDirection n) (U : Vec4) :
    rotation n *ᵥ directionalFlux n U = xFlux (rotate n U) := by
  have hp : (n 0^2+n 1^2)*pressure U = pressure U := by rw [hn]; ring
  simp only [directionalFlux, xFlux, yFlux, pressure_rotate n hn]
  ext i
  fin_cases i <;>
    simp [velocity, transverseVelocity, rotation, rotate_eq,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> ring_nf
  all_goals nlinarith [hp]

theorem directionalFlux_rotation (n : Direction) (hn : UnitDirection n) (U : Vec4) :
    directionalFlux n U = (rotation n).transpose *ᵥ xFlux (rotate n U) := by
  rw [← rotate_directionalFlux n hn, Matrix.mulVec_mulVec,
    transpose_mul_rotation n hn, Matrix.one_mulVec]

#print axioms pressure_rotate
#print axioms directionalFlux_rotation

end
end Project.Euler2DConservative.RealFlux
