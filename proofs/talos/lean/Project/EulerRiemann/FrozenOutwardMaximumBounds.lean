import Project.EulerRiemann.FrozenOutwardMaximumSpec

namespace Project.EulerRiemann.Frozen.OutwardMaximum
open Project.ProofKit.F64Outward (Checked rejected)
open Project.ProofKit.F64Order
open Project.Euler2DCellStep.Sweep (State orient)
open Project.Euler2DConservative.Guard (StateBounds decodedState)
open Project.Euler2DConservative.RealFlux (eigenvalues velocity soundSpeed)
open CodeLib.IEEE64

def Bounds (state : State) (alpha : UInt64) : Prop :=
  StateBounds state.density state.mx state.my state.energy ∧
    ∀ i : Fin 4, |eigenvalues
      (velocity (decodedState state.density state.mx state.my state.energy))
      (soundSpeed (decodedState state.density state.mx state.my state.energy)) i| ≤ value alpha

theorem bounds_mono {state : State} {alpha beta : UInt64}
    (h : Bounds state alpha) (hle : value alpha ≤ value beta) : Bounds state beta :=
  ⟨h.1, fun i => (h.2 i).trans hle⟩

theorem side_bounds (state : State)
    (h : (OutwardSpeed.speedUpper state.density state.mx state.my state.energy).status = 0) :
    Bounds state (OutwardSpeed.speedUpper state.density state.mx state.my state.energy).value :=
  ⟨(OutwardSpeed.speed_upper _ _ _ _ h).1, OutwardSpeed.speed_eigenvalue_bound _ _ _ _ h⟩

theorem interface_bounds (left right : State) (h : (interfaceUpper left right).status = 0) :
    positiveBits (interfaceUpper left right).value = true ∧
      Bounds left (interfaceUpper left right).value ∧
      Bounds right (interfaceUpper left right).value := by
  have hs := (interface_status left right).mp h
  have hm := merge_upper _ _ h (OutwardSpeed.speed_positive _ _ _ _ hs.1)
    (OutwardSpeed.speed_positive _ _ _ _ hs.2)
  refine ⟨hm.1, bounds_mono (side_bounds left hs.1) ?_,
    bounds_mono (side_bounds right hs.2) ?_⟩
  · rw [interfaceUpper, hm.2]
    exact le_max_left _ _
  · rw [interfaceUpper, hm.2]
    exact le_max_right _ _

theorem cell_bounds (state : State) (h : (cellUpper state).status = 0) :
    Bounds state (cellUpper state).value ∧
      Bounds (orient true state) (cellUpper state).value := by
  have hs := (cell_status state).mp h
  have hm := merge_upper _ _ h (OutwardSpeed.speed_positive _ _ _ _ hs.1)
    (OutwardSpeed.speed_positive _ _ _ _ hs.2)
  refine ⟨bounds_mono (side_bounds state hs.1) ?_,
    bounds_mono (side_bounds (orient true state) hs.2) ?_⟩
  · rw [cellUpper, hm.2]
    exact le_max_left _ _
  · rw [cellUpper, hm.2]
    exact le_max_right _ _

theorem interface_behavior (left right : State) :
    interfaceUpper left right = rejected ∨
      (interfaceUpper left right).status = 0 ∧
      CodeLib.IEEE64.Finite (interfaceUpper left right).value ∧
      Bounds left (interfaceUpper left right).value ∧
      Bounds right (interfaceUpper left right).value := by
  rcases merge_result
    (OutwardSpeed.speedUpper left.density left.mx left.my left.energy)
    (OutwardSpeed.speedUpper right.density right.mx right.my right.energy) with hr | h
  · exact Or.inl hr
  · have hb := interface_bounds left right h
    exact Or.inr ⟨h, (positiveBits_spec _ hb.1).1, hb.2⟩

#print axioms interface_bounds
#print axioms cell_bounds
#print axioms interface_behavior

end Project.EulerRiemann.Frozen.OutwardMaximum
