import Library.Arrays.Search.Program
import LeanExe.IR.Combinators

namespace Library.Arrays.Search

open LeanExe.IR

/-- One step of `firstZero`'s loop. -/
def firstZeroStep (xs : Array UInt64) (count i k : UInt64) : UInt64 :=
  if k == count && xs[i.toNat]! == 0 then i else k

/-- `firstZero` gives `count` when the first `count` words hold no zero, and otherwise the index
of the first zero. -/
theorem firstZero_cases (xs : Array UInt64) (count : UInt64) :
    (firstZero xs count = count ∧ ∀ j < count.toNat, xs[j]! ≠ 0) ∨
    (∃ j < count.toNat, firstZero xs count = UInt64.ofNat j ∧ xs[j]! = 0 ∧
      ∀ i < j, xs[i]! ≠ 0) := by
  have hc := count.toNat_lt
  refine loop_induction (P := fun m k => (k = count ∧ ∀ j < m, xs[j]! ≠ 0) ∨
    (∃ j < m, k = UInt64.ofNat j ∧ xs[j]! = 0 ∧ ∀ i < j, xs[i]! ≠ 0))
    (Or.inl ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩) ?_
  intro m k hm hP
  have hmt : (UInt64.ofNat m).toNat = m := UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hm hc)
  rcases hP with ⟨rfl, hnz⟩ | ⟨j, hj, rfl, hz, hb⟩
  · by_cases hx : xs[m]! = 0
    · exact Or.inr ⟨m, by omega, by simp [hmt, hx], hx, hnz⟩
    · refine Or.inl ⟨by simp [hmt, hx], fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact hnz j h
      · exact hx
  · have hne : UInt64.ofNat j ≠ count := fun h => by
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (by omega : j < count.toNat) hc)] at this
      omega
    exact Or.inr ⟨j, by omega, by simp [hne], hz, hb⟩

end Library.Arrays.Search
