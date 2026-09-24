import Project.EulerRiemann.FrozenOutwardAdvance
import Project.EulerRiemann.FrozenOutwardSideSpec
import Project.EulerRiemann.FrozenOutwardConstants
import Project.ProofKit.F64OutwardAccepted
import Project.ProofKit.F64OrderComplete

namespace Project.EulerRiemann.Frozen.OutwardNumerics
open Project.Euler2DConservative.Model (positiveBits)
open Project.Euler2DDynamicFlux.Model (CheckedFlux)
open Project.Euler2DCellStep.Model (CheckedCell rejectedCell updateCheckedBits)
open Project.ProofKit.F64Order
  (positiveBits_spec abs_value_mono absBits_of_positive positiveBits_of_finite_value_pos)
open CodeLib.IEEE64

theorem advance_parts (ratio rho mx my energy : UInt64) (left right : CheckedFlux)
    (h : (advanceCheckedBits ratio rho mx my energy left right).status = 0) :
    let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
    let courant := Project.ProofKit.F64Outward.mul true ratio alpha
    let density := updateCheckedBits ratio rho left.mass right.mass
    let momentum := updateCheckedBits ratio mx left.momentum right.momentum
    let transverse := updateCheckedBits ratio my left.transverse right.transverse
    let nextEnergy := updateCheckedBits ratio energy left.energy right.energy
    positiveBits ratio = true ∧ left.status = 0 ∧ right.status = 0 ∧
      positiveBits alpha = true ∧ courant.status = 0 ∧
      courant.value ≤ 0x3FE0000000000000 ∧
      density.status = 0 ∧ momentum.status = 0 ∧ transverse.status = 0 ∧
      nextEnergy.status = 0 ∧
      (sideCheckedBits density.value momentum.value transverse.value nextEnergy.value).status = 0 := by
  unfold advanceCheckedBits at h
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [rejectedCell]

theorem advance_values (ratio rho mx my energy : UInt64) (left right : CheckedFlux)
    (h : (advanceCheckedBits ratio rho mx my energy left right).status = 0) :
    let alpha := if left.alpha ≤ right.alpha then right.alpha else left.alpha
    let density := updateCheckedBits ratio rho left.mass right.mass
    let momentum := updateCheckedBits ratio mx left.momentum right.momentum
    let transverse := updateCheckedBits ratio my left.transverse right.transverse
    let nextEnergy := updateCheckedBits ratio energy left.energy right.energy
    advanceCheckedBits ratio rho mx my energy left right =
      ⟨0, density.value, momentum.value, transverse.value, nextEnergy.value,
        (sideCheckedBits density.value momentum.value transverse.value nextEnergy.value).pressure,
        alpha, (Project.ProofKit.F64Outward.mul true ratio alpha).value⟩ := by
  unfold advanceCheckedBits at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simp_all [rejectedCell]

theorem advance_alpha (ratio rho mx my energy : UInt64) (left right : CheckedFlux)
    (h : (advanceCheckedBits ratio rho mx my energy left right).status = 0) :
    (advanceCheckedBits ratio rho mx my energy left right).alpha =
      if left.alpha ≤ right.alpha then right.alpha else left.alpha := by
  rw [advance_values ratio rho mx my energy left right h]

theorem advance_state (ratio rho mx my energy : UInt64) (left right : CheckedFlux)
    (h : (advanceCheckedBits ratio rho mx my energy left right).status = 0) :
    let out := advanceCheckedBits ratio rho mx my energy left right
    Project.Euler2DConservative.Guard.StateBounds
      out.density out.momentum out.transverse out.energy ∧
      positiveBits out.pressure = true := by
  have hs := (advance_parts ratio rho mx my energy left right h).2.2.2.2.2.2.2.2.2.2
  dsimp only
  rw [advance_values ratio rho mx my energy left right h]
  exact ⟨(side_bounds _ _ _ _ hs).1, side_pressure_positive _ _ _ _ hs⟩

theorem advance_courant (ratio rho mx my energy : UInt64) (left right : CheckedFlux)
    (h : (advanceCheckedBits ratio rho mx my energy left right).status = 0) :
    let out := advanceCheckedBits ratio rho mx my energy left right
    positiveBits ratio = true ∧ positiveBits out.alpha = true ∧
      Finite out.courant ∧ 0 < value out.courant ∧
      value ratio * value out.alpha ≤ value out.courant ∧
      value out.courant ≤ (1 : ℝ) / 2 := by
  obtain ⟨hr, _, _, ha, hc, hb, _⟩ := advance_parts ratio rho mx my energy left right h
  have hm := Project.ProofKit.F64Outward.sound_upper
    (Project.ProofKit.F64Outward.mul_accepted true ratio _ hc).2.2
  have hp := (mul_pos (positiveBits_spec ratio hr).2 (positiveBits_spec _ ha).2).trans_le hm.2
  have pc := positiveBits_of_finite_value_pos _ hm.1 hp
  have ph : positiveBits 0x3FE0000000000000 = true := by decide
  have hle := abs_value_mono
    (Project.ProofKit.F64Outward.mul true ratio
      (if left.alpha ≤ right.alpha then right.alpha else left.alpha)).value
    0x3FE0000000000000 (by
    simpa only [absBits_of_positive _ pc, absBits_of_positive _ ph] using hb)
  rw [abs_of_pos hp, OutwardSpeed.half_value,
    abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] at hle
  dsimp only
  rw [advance_values ratio rho mx my energy left right h]
  exact ⟨hr, ha, hm.1, hp, hm.2, hle⟩

theorem advance_result (ratio rho mx my energy : UInt64) (left right : CheckedFlux) :
    advanceCheckedBits ratio rho mx my energy left right = rejectedCell ∨
      (advanceCheckedBits ratio rho mx my energy left right).status = 0 := by
  unfold advanceCheckedBits
  dsimp only
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

theorem advance_behavior (ratio rho mx my energy : UInt64) (left right : CheckedFlux) :
    let out := advanceCheckedBits ratio rho mx my energy left right
    out = rejectedCell ∨ out.status = 0 ∧
      Project.Euler2DConservative.Guard.StateBounds
        out.density out.momentum out.transverse out.energy ∧
      positiveBits out.pressure = true ∧
      positiveBits ratio = true ∧ positiveBits out.alpha = true ∧
      Finite out.courant ∧ 0 < value out.courant ∧
      value ratio * value out.alpha ≤ value out.courant ∧
      value out.courant ≤ (1 : ℝ) / 2 := by
  rcases advance_result ratio rho mx my energy left right with hr | hs
  · exact Or.inl hr
  · exact Or.inr ⟨hs, (advance_state ratio rho mx my energy left right hs).1,
      (advance_state ratio rho mx my energy left right hs).2,
      advance_courant ratio rho mx my energy left right hs⟩

#print axioms advance_parts
#print axioms advance_values
#print axioms advance_alpha
#print axioms advance_state
#print axioms advance_courant
#print axioms advance_behavior
end Project.EulerRiemann.Frozen.OutwardNumerics
