import Mathlib.Tactic

namespace Project.ProofKit.GreedyMaximum

def index (score : Nat → Int) : Nat → Nat
  | 0 => 0
  | count + 1 => if score (index score count) < score count then count else index score count

theorem first_maximum (score : Nat → Int) (count : Nat) (hCount : 0 < count) :
    index score count < count ∧
      (∀ i < count, score i ≤ score (index score count)) ∧
      (∀ i < count, score i = score (index score count) → index score count ≤ i) := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases hZero : count = 0
    · subst count
      simp only [index, lt_self_iff_false, ite_false]
      refine ⟨by omega, ?_, fun i _ _ => Nat.zero_le i⟩
      intro i hi
      have hZero : i = 0 := by omega
      simp only [hZero, le_refl]
    · obtain ⟨hIndex, hMax, hFirst⟩ := ih (by omega)
      rw [index]
      split
      · rename_i hGreater
        refine ⟨by omega, ?_, ?_⟩
        · intro i hi
          by_cases hLast : i = count
          · simp [hLast]
          · exact (hMax i (by omega)).trans hGreater.le
        · intro i hi hEq
          by_cases hLast : i = count
          · omega
          · have := hMax i (by omega)
            omega
      · rename_i hNotGreater
        refine ⟨by omega, ?_, ?_⟩
        · intro i hi
          by_cases hLast : i = count
          · subst i
            omega
          · exact hMax i (by omega)
        · intro i hi hEq
          by_cases hLast : i = count
          · omega
          · exact hFirst i (by omega) hEq

theorem unique (score : Nat → Int) (count winner : Nat) (hWinner : winner < count)
    (hUnique : ∀ i < count, i ≠ winner → score i < score winner) :
    index score count = winner := by
  obtain ⟨hIndex, hMax, _⟩ := first_maximum score count (by omega)
  by_contra hNe
  have := hUnique (index score count) hIndex hNe
  have := hMax winner hWinner
  omega

#print axioms first_maximum
#print axioms unique
end Project.ProofKit.GreedyMaximum
