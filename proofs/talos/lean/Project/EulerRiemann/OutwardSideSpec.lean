import Project.EulerRiemann.OutwardSide
import Project.EulerRiemann.OutwardMaximumBounds
import Project.EulerRiemann.NumericsSideFinite

namespace Project.EulerRiemann.OutwardNumerics
open Project.Euler2DConservative.Model (finiteBits positiveBits rejectedSide)
open Project.ProofKit.F64Order (finiteBits_iff positiveBits_spec)
open Project.Euler2DCellStep.Sweep (State)

theorem side_values_of_accepted (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    let u := Wasm.IEEE64.div mx rho
    let v := Wasm.IEEE64.div my rho
    let tx := Wasm.IEEE64.mul mx u
    let ty := Wasm.IEEE64.mul my v
    let internal := Wasm.IEEE64.sub energy (Wasm.IEEE64.mul 0x3FE0000000000000 (Wasm.IEEE64.add tx ty))
    let pressure := Wasm.IEEE64.mul 0x3FD999999999999A internal
    sideCheckedBits rho mx my energy =
      ⟨0, u, pressure, (OutwardSpeed.speedUpper rho mx my energy).value, mx,
        Wasm.IEEE64.add tx pressure, Wasm.IEEE64.mul my u,
        Wasm.IEEE64.mul u (Wasm.IEEE64.add energy pressure)⟩ := by
  unfold sideCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [rejectedSide]

theorem side_speed_accepted (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    (OutwardSpeed.speedUpper rho mx my energy).status = 0 := by
  unfold sideCheckedBits at h
  dsimp only at h
  split at h
  · rename_i hs
    simpa only [beq_iff_eq] using hs
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem side_speed_value (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    (sideCheckedBits rho mx my energy).speed =
      (OutwardSpeed.speedUpper rho mx my energy).value := by
  rw [side_values_of_accepted rho mx my energy h]

theorem side_pressure_positive (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    positiveBits (sideCheckedBits rho mx my energy).pressure = true := by
  unfold sideCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢
  all_goals
    first
    | exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    | rename_i hSpeed hKinetic hOutput
      simp only [Bool.and_eq_true] at hOutput
      exact hOutput.1.1.1.1

theorem accepted_side_finite (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    Numerics.SideFinite rho mx my energy := by
  unfold sideCheckedBits at h
  dsimp only at h
  split_ifs at h
  all_goals
    first
    | exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    | rename_i hSpeed hKinetic hOutput
      simp only [Bool.and_eq_true] at hKinetic hOutput
      obtain ⟨⟨⟨⟨⟨⟨hu, htx⟩, hv⟩, hty⟩, htotal⟩, hkinetic⟩, hi⟩ := hKinetic
      obtain ⟨⟨⟨⟨hp, hnormal⟩, htransverse⟩, henthalpy⟩, heflux⟩ := hOutput
      exact ⟨(finiteBits_iff _).mp hu, (finiteBits_iff _).mp hv,
        (finiteBits_iff _).mp htx, (finiteBits_iff _).mp hty,
        (finiteBits_iff _).mp htotal, (finiteBits_iff _).mp hkinetic,
        (positiveBits_spec _ hi).1, (positiveBits_spec _ hp).1,
        (finiteBits_iff _).mp hnormal, (finiteBits_iff _).mp htransverse,
        (finiteBits_iff _).mp henthalpy, (finiteBits_iff _).mp heflux⟩

theorem side_bounds (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    OutwardMaximum.Bounds (⟨rho, mx, my, energy⟩ : State)
      (sideCheckedBits rho mx my energy).speed := by
  rw [side_speed_value rho mx my energy h]
  exact OutwardMaximum.side_bounds _ (side_speed_accepted rho mx my energy h)

theorem side_speed_positive (rho mx my energy : UInt64)
    (h : (sideCheckedBits rho mx my energy).status = 0) :
    positiveBits (sideCheckedBits rho mx my energy).speed = true := by
  rw [side_speed_value rho mx my energy h]
  exact OutwardSpeed.speed_positive rho mx my energy (side_speed_accepted rho mx my energy h)

theorem side_result (rho mx my energy : UInt64) :
    sideCheckedBits rho mx my energy = rejectedSide ∨
      (sideCheckedBits rho mx my energy).status = 0 := by
  unfold sideCheckedBits
  dsimp only
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem side_behavior (rho mx my energy : UInt64) :
    sideCheckedBits rho mx my energy = rejectedSide ∨
      (sideCheckedBits rho mx my energy).status = 0 ∧
      OutwardMaximum.Bounds (⟨rho, mx, my, energy⟩ : State)
        (sideCheckedBits rho mx my energy).speed ∧
      positiveBits (sideCheckedBits rho mx my energy).speed = true ∧
      positiveBits (sideCheckedBits rho mx my energy).pressure = true ∧
      Numerics.SideFinite rho mx my energy := by
  rcases side_result rho mx my energy with hr | hs
  · exact Or.inl hr
  · exact Or.inr ⟨hs, side_bounds rho mx my energy hs,
      side_speed_positive rho mx my energy hs, side_pressure_positive rho mx my energy hs,
      accepted_side_finite rho mx my energy hs⟩

#print axioms side_values_of_accepted
#print axioms side_speed_accepted
#print axioms accepted_side_finite
#print axioms side_bounds
#print axioms side_behavior
end Project.EulerRiemann.OutwardNumerics
