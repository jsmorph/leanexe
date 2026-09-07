import Project.EulerConservative.Safety

namespace Project.EulerConservative.Safety

/-- The rounded pressure and signal speed are strictly positive finite words. -/
theorem accepted_outputPositive (rho momentum energy : UInt64)
    (h : (Model.sideCheckedBits rho momentum energy).status = 0) :
    Model.positiveBits (Model.sideCheckedBits rho momentum energy).pressure = true ∧
    Model.positiveBits (Model.sideCheckedBits rho momentum energy).speed = true := by
  generalize hresult : Model.sideCheckedBits rho momentum energy = result at h ⊢
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
          obtain ⟨hthird2, _⟩ := Bool.and_eq_true_iff.mp hthird3
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
end Project.EulerConservative.Safety
