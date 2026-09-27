import Project.EulerRiemann.RealRusanov
import Project.Euler2DConservative.RealCharacteristicSpeed
import Project.ProofKit.RealLaxFriedrichs

namespace Project.EulerRiemann.RealRusanov
open Project.Euler2DConservative
open Project.Euler2DConservative.Guard (Vec4)
open Project.ProofKit.RealLaxFriedrichs

theorem physicalFlux_eq_xFlux (U : Vec4) : physicalFlux U = RealFlux.xFlux U := by
  funext i
  fin_cases i <;> simp [physicalFlux, RealFlux.xFlux, RealFlux.velocity] <;> ring

theorem interfaceFlux_eq_numericalFlux (a : ℝ) (L R : Vec4) :
    interfaceFlux a L R = numericalFlux RealFlux.xFlux a L R := by
  funext i
  change (physicalFlux L i+physicalFlux R i)/2-a*(R i-L i)/2 =
    (RealFlux.xFlux L i+RealFlux.xFlux R i)/2-a*(R i-L i)/2
  rw [physicalFlux_eq_xFlux, physicalFlux_eq_xFlux]

theorem interface_consistent (a : ℝ) (U : Vec4) :
    interfaceFlux a U U = RealFlux.xFlux U := by
  rw [interfaceFlux_eq_numericalFlux]
  exact numericalFlux_consistent _ _ _

theorem interface_left_fluctuation (a : ℝ) (L R : Vec4) :
    interfaceFlux a L R = RealFlux.xFlux L+
      fluctuationMinus a (R-L) (RealFlux.xFlux R-RealFlux.xFlux L) := by
  rw [interfaceFlux_eq_numericalFlux]
  exact numericalFlux_left _ _ _ _

theorem interface_right_fluctuation (a : ℝ) (L R : Vec4) :
    interfaceFlux a L R = RealFlux.xFlux R-
      fluctuationPlus a (R-L) (RealFlux.xFlux R-RealFlux.xFlux L) := by
  rw [interfaceFlux_eq_numericalFlux]
  exact numericalFlux_right _ _ _ _

theorem directional_wave_identities (n : RealFlux.Direction) (a : ℝ) (ha : a ≠ 0)
    (L R : Vec4) :
    let jump := R-L
    let fluxJump := RealFlux.directionalFlux n R-RealFlux.directionalFlux n L
    waveMinus a jump fluxJump+wavePlus a jump fluxJump = jump ∧
      -a • waveMinus a jump fluxJump+a • wavePlus a jump fluxJump = fluxJump :=
  ⟨wave_sum _ _ _, weighted_wave_sum _ ha _ _⟩

theorem directional_flux_reverse (n : RealFlux.Direction) (U : Vec4) :
    RealFlux.directionalFlux (-n) U = -RealFlux.directionalFlux n U := by
  funext i
  simp only [RealFlux.directionalFlux, Pi.neg_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem directional_interface_reverse (n : RealFlux.Direction) (a : ℝ) (L R : Vec4) :
    numericalFlux (RealFlux.directionalFlux (-n)) a R L =
      -numericalFlux (RealFlux.directionalFlux n) a L R := by
  have h : RealFlux.directionalFlux (-n) = fun U => -RealFlux.directionalFlux n U :=
    funext (directional_flux_reverse n)
  rw [h]
  exact numericalFlux_reverse _ _ _ _

#print axioms physicalFlux_eq_xFlux
#print axioms directional_wave_identities
#print axioms directional_interface_reverse
end Project.EulerRiemann.RealRusanov
