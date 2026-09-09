import Project.Euler2DConservative.Safety

namespace Project.Euler2DConservative.Safety

/-- The rounded pressure and signal speed are strictly positive finite words. -/
theorem accepted_outputPositive (rho momentum transverse energy : UInt64)
    (h : (Model.sideCheckedBits rho momentum transverse energy).status = 0) :
    Model.positiveBits (Model.sideCheckedBits rho momentum transverse energy).pressure = true ∧
    Model.positiveBits (Model.sideCheckedBits rho momentum transverse energy).speed = true := by
  generalize hresult : Model.sideCheckedBits rho momentum transverse energy = result at h ⊢
  unfold Model.sideCheckedBits at hresult
  split at hresult
  · dsimp only at hresult
    split at hresult
    · split at hresult
      · rename_i hsecond
        split at hresult
        · rename_i hthird
          subst result
          obtain ⟨hsecond2, _⟩ := Bool.and_eq_true_iff.mp hsecond
          obtain ⟨hp, _⟩ := Bool.and_eq_true_iff.mp hsecond2
          obtain ⟨hthird4, _⟩ := Bool.and_eq_true_iff.mp hthird
          obtain ⟨hthird3, _⟩ := Bool.and_eq_true_iff.mp hthird4
          obtain ⟨hthird22, _⟩ := Bool.and_eq_true_iff.mp hthird3
          obtain ⟨hthird2, _⟩ := Bool.and_eq_true_iff.mp hthird22
          obtain ⟨_, hs⟩ := Bool.and_eq_true_iff.mp hthird2
          exact ⟨hp, hs⟩
        · subst result
          exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
      · subst result
        exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
    · subst result
      exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)
  · subst result
    exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

#print axioms accepted_outputPositive
end Project.Euler2DConservative.Safety
