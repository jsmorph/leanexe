import Project.EulerRiemann.FrozenOutwardThermodynamics
import Project.EulerRiemann.FrozenNumericsSafety
import Project.Euler2DConservative.RealCharacteristicSpeed

namespace Project.EulerRiemann.Frozen.OutwardSpeed
open CodeLib.IEEE64
open Project.ProofKit.F64Outward
open Project.ProofKit.F64Order
open Project.Euler2DConservative.Guard (StateBounds internalEnergy decodedState)
open Project.Euler2DConservative.RealFlux (velocity soundSpeed eigenvalues)

theorem acoustic_upper (rho mx my energy : UInt64) (hr : 0 < value rho)
    (hi : 0 < internalEnergy (decodedState rho mx my energy))
    (h : (soundUpper rho mx my energy).status = 0) :
    Finite (soundUpper rho mx my energy).value ∧
    soundSpeed (decodedState rho mx my energy) ≤ value (soundUpper rho mx my energy).value := by
  let radicand := radicandUpper rho mx my energy
  unfold soundUpper at h ⊢
  dsimp only at h ⊢
  split_ifs at h with hrStatus
  · simp only [hrStatus, ite_true]
    have hrStatus : radicand.status = 0 := by simpa [radicand] using hrStatus
    have er := radicand_upper rho mx my energy hr hi hrStatus
    have es := sound_upper (sqrt_accepted true radicand.value h).2.2
    refine ⟨es.1, le_trans ?_ es.2⟩
    apply Real.sqrt_le_sqrt
    change (7/5:ℝ)*Project.Euler2DConservative.Guard.pressure (decodedState rho mx my energy)/value rho ≤
      value (radicandUpper rho mx my energy).value
    simpa only [mul_div_assoc] using er.2
  · exact False.elim ((by decide : (1:UInt64) ≠ 0) h)

theorem speed_inputGuard (rho mx my energy : UInt64)
    (h : (speedUpper rho mx my energy).status = 0) :
    Numerics.stateGuard rho mx my energy = true := by
  unfold speedUpper at h
  split at h
  · assumption
  · exact False.elim ((by decide : (1:UInt64) ≠ 0) h)

theorem speed_upper (rho mx my energy : UInt64)
    (h : (speedUpper rho mx my energy).status = 0) :
    StateBounds rho mx my energy ∧ Finite (speedUpper rho mx my energy).value ∧
    |velocity (decodedState rho mx my energy)|+soundSpeed (decodedState rho mx my energy) ≤
      value (speedUpper rho mx my energy).value := by
  have hg := speed_inputGuard rho mx my energy h
  have hb := Numerics.stateGuard_spec rho mx my energy hg
  refine ⟨hb, ?_⟩
  let v := div true (absBits mx) rho
  let s := soundUpper rho mx my energy
  simp only [speedUpper, hg, ite_true] at h ⊢
  split_ifs at h with hs
  · simp only [hs, ite_true]
    have hs : v.status = 0 ∧ s.status = 0 := by simpa [v, s] using hs
    have ev := sound_upper (div_accepted true (absBits mx) rho hs.1).2.2.2
    have es := acoustic_upper rho mx my energy hb.densityPositive hb.internalPositive hs.2
    have ea := sound_upper (add_accepted true v.value s.value h).2.2
    have eu : |velocity (decodedState rho mx my energy)| ≤ value v.value := by
      simpa only [velocity, decodedState, Matrix.cons_val_one, Matrix.cons_val_zero,
        abs_div, abs_of_pos hb.densityPositive, absBits_value] using ev.2
    exact ⟨ea.1, (add_le_add eu es.2).trans ea.2⟩
  · exact False.elim ((by decide : (1:UInt64) ≠ 0) h)

theorem speed_eigenvalue_bound (rho mx my energy : UInt64)
    (h : (speedUpper rho mx my energy).status = 0) (i : Fin 4) :
    |eigenvalues (velocity (decodedState rho mx my energy))
      (soundSpeed (decodedState rho mx my energy)) i| ≤
        value (speedUpper rho mx my energy).value := by
  have hs := speed_upper rho mx my energy h
  exact (Project.Euler2DConservative.RealFlux.eigenvalue_abs_le _ _
    (Real.sqrt_nonneg _) i).trans hs.2.2

theorem speed_positive (rho mx my energy : UInt64)
    (h : (speedUpper rho mx my energy).status = 0) :
    positiveBits (speedUpper rho mx my energy).value = true := by
  have hs := speed_upper rho mx my energy h
  have had : Project.Euler2DConservative.Guard.Admissible (decodedState rho mx my energy) :=
    ⟨hs.1.densityPositive, mul_pos (by norm_num : (0:ℝ) < 2/5) hs.1.internalPositive⟩
  apply positiveBits_of_finite_value_pos _ hs.2.1
  exact (add_pos_of_nonneg_of_pos (abs_nonneg _)
    (Project.Euler2DConservative.RealFlux.soundSpeed_pos _ had)).trans_le hs.2.2

theorem speed_result (rho mx my energy : UInt64) :
    speedUpper rho mx my energy = rejected ∨
      (speedUpper rho mx my energy).status = 0 := by
  unfold speedUpper
  dsimp only
  split_ifs
  · exact (add_behavior true _ _).imp id (fun h => h.2.2.1)
  all_goals exact Or.inl rfl

theorem speed_behavior (rho mx my energy : UInt64) :
    speedUpper rho mx my energy = rejected ∨
      (speedUpper rho mx my energy).status = 0 ∧
      StateBounds rho mx my energy ∧
      positiveBits (speedUpper rho mx my energy).value = true ∧
      ∀ i : Fin 4, |eigenvalues (velocity (decodedState rho mx my energy))
        (soundSpeed (decodedState rho mx my energy)) i| ≤
          value (speedUpper rho mx my energy).value := by
  rcases speed_result rho mx my energy with hr | hs
  · exact Or.inl hr
  · exact Or.inr ⟨hs, (speed_upper rho mx my energy hs).1,
      speed_positive rho mx my energy hs, speed_eigenvalue_bound rho mx my energy hs⟩

#print axioms acoustic_upper
#print axioms speed_upper
#print axioms speed_eigenvalue_bound
#print axioms speed_positive
#print axioms speed_behavior
end Project.EulerRiemann.Frozen.OutwardSpeed
