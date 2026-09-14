import Project.EulerRiemann.OutwardKinetic
import Project.Euler2DConservative.Guard

namespace Project.EulerRiemann.OutwardSpeed
open CodeLib.IEEE64
open Project.ProofKit.F64Outward
open Project.Euler2DConservative.Guard (internalEnergy pressure decodedState)
set_option exponentiation.threshold 4096

theorem internal_upper (rho mx my energy : UInt64) (hr : 0 < value rho)
    (h : (internalUpper rho mx my energy).status = 0) :
    Finite (internalUpper rho mx my energy).value ∧
    internalEnergy (decodedState rho mx my energy) ≤ value (internalUpper rho mx my energy).value := by
  let kinetic := kineticLower rho mx my
  unfold internalUpper at h ⊢
  dsimp only at h ⊢
  split_ifs at h with hk
  · simp only [hk, ite_true]
    have hk : kinetic.status = 0 := by simpa [kinetic] using hk
    have ek := kinetic_lower rho mx my hr hk
    have es := sound_upper (sub_accepted true energy kinetic.value h).2.2
    refine ⟨es.1, le_trans ?_ es.2⟩
    change value energy-((value mx)^2+(value my)^2)/(2*value rho) ≤ value energy-value kinetic.value
    exact sub_le_sub_left ek.2 _
  · exact False.elim ((by decide : (1:UInt64) ≠ 0) h)

theorem pressure_upper (rho mx my energy : UInt64) (hr : 0 < value rho)
    (hi : 0 < internalEnergy (decodedState rho mx my energy))
    (h : (pressureUpper rho mx my energy).status = 0) :
    Finite (pressureUpper rho mx my energy).value ∧
    pressure (decodedState rho mx my energy) ≤ value (pressureUpper rho mx my energy).value := by
  let internal := internalUpper rho mx my energy
  unfold pressureUpper at h ⊢
  dsimp only at h ⊢
  split_ifs at h with hiStatus
  · simp only [hiStatus, ite_true]
    have hiStatus : internal.status = 0 := by simpa [internal] using hiStatus
    have ei := internal_upper rho mx my energy hr hiStatus
    have em := sound_upper (mul_accepted true 0x3FD999999999999A internal.value h).2.2
    refine ⟨em.1, le_trans ?_ em.2⟩
    exact mul_le_mul pressure_factor_upper ei.2 hi.le
      ((by norm_num : (0:ℝ) ≤ 2/5).trans pressure_factor_upper)
  · exact False.elim ((by decide : (1:UInt64) ≠ 0) h)

theorem radicand_upper (rho mx my energy : UInt64) (hr : 0 < value rho)
    (hi : 0 < internalEnergy (decodedState rho mx my energy))
    (h : (radicandUpper rho mx my energy).status = 0) :
    Finite (radicandUpper rho mx my energy).value ∧
    (7/5:ℝ)*(pressure (decodedState rho mx my energy)/value rho) ≤
      value (radicandUpper rho mx my energy).value := by
  let p := pressureUpper rho mx my energy
  let ratio := div true p.value rho
  unfold radicandUpper at h ⊢
  dsimp only at h ⊢
  split_ifs at h with hp hratio
  · simp only [hp, hratio, ite_true]
    have hp : p.status = 0 := by simpa [p] using hp
    have hratio : ratio.status = 0 := by simpa [ratio, p] using hratio
    have ep := pressure_upper rho mx my energy hr hi hp
    have ed := sound_upper (div_accepted true p.value rho hratio).2.2.2
    have em := sound_upper (mul_accepted true 0x3FF6666666666667 ratio.value h).2.2
    have er : pressure (decodedState rho mx my energy)/value rho ≤ value ratio.value :=
      (div_le_div_of_nonneg_right ep.2 hr.le).trans ed.2
    have hpNonnegative : 0 ≤ pressure (decodedState rho mx my energy)/value rho :=
      div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2/5) hi.le) hr.le
    refine ⟨em.1, le_trans ?_ em.2⟩
    exact mul_le_mul sound_factor_upper er hpNonnegative
      ((by norm_num : (0:ℝ) ≤ 7/5).trans sound_factor_upper)
  all_goals exact False.elim ((by decide : (1:UInt64) ≠ 0) h)

#print axioms internal_upper
#print axioms pressure_upper
#print axioms radicand_upper
end Project.EulerRiemann.OutwardSpeed
