import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace Project.ProofKit.RealFiniteVolumeBalance
open scoped BigOperators

theorem telescope (flux : Nat → ℝ) (count : Nat) :
    ∑ i ∈ Finset.range count, (flux (i+1)-flux i) = flux count-flux 0 := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem sweep_balance (count : Nat) (ratio : ℝ)
    (before after flux residual : Nat → ℝ)
    (h : ∀ i < count, after i = before i-ratio*(flux (i+1)-flux i)+residual i) :
    (∑ i ∈ Finset.range count, after i)-(∑ i ∈ Finset.range count, before i) =
      -ratio*(flux count-flux 0)+(∑ i ∈ Finset.range count, residual i) := by
  have hs : (∑ i ∈ Finset.range count, after i) =
      ∑ i ∈ Finset.range count, (before i-ratio*(flux (i+1)-flux i)+residual i) :=
    Finset.sum_congr rfl (fun i hi => h i (Finset.mem_range.mp hi))
  rw [hs, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, telescope]
  ring

theorem time_balance (count : Nat) (total boundary residual : Nat → ℝ)
    (h : ∀ i < count, total (i+1)-total i = boundary i+residual i) :
    total count-total 0 = (∑ i ∈ Finset.range count, boundary i)+
      (∑ i ∈ Finset.range count, residual i) := by
  rw [← telescope total count, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi => h i (Finset.mem_range.mp hi))

#print axioms sweep_balance
#print axioms time_balance
end Project.ProofKit.RealFiniteVolumeBalance
