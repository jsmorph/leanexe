import Project.ProofKit.F64OutwardAccepted
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Project.ProofKit.F64Outward
open CodeLib.IEEE64
open scoped BigOperators

theorem add_sound (up : Bool) (a b : Checked) (x y : ℝ)
    (ha : Sound up a x) (hb : Sound up b y)
    (hs : (add up a.value b.value).status = 0) :
    Sound up (add up a.value b.value) (x + y) := by
  have h := (add_accepted up a.value b.value hs).2.2
  refine ⟨h.1, h.2.1, ?_⟩
  cases up
  · exact h.2.2.trans (add_le_add ha.2.2 hb.2.2)
  · exact (add_le_add ha.2.2 hb.2.2).trans h.2.2

theorem sub_sound (up : Bool) (a b : Checked) (x y : ℝ)
    (ha : Sound up a x) (hb : Sound (!up) b y)
    (hs : (sub up a.value b.value).status = 0) :
    Sound up (sub up a.value b.value) (x - y) := by
  have h := (sub_accepted up a.value b.value hs).2.2
  refine ⟨h.1, h.2.1, ?_⟩
  cases up
  · exact h.2.2.trans (sub_le_sub ha.2.2 hb.2.2)
  · exact (sub_le_sub ha.2.2 hb.2.2).trans h.2.2

theorem sum_range_sound (up : Bool) (acc term : Nat → Checked)
    (x : Nat → ℝ) (initial : ℝ) (n : Nat)
    (hInitial : Sound up (acc 0) initial)
    (hTerm : ∀ k < n, Sound up (term k) (x k))
    (hStep : ∀ k < n, acc (k + 1) = add up (acc k).value (term k).value)
    (hAccepted : ∀ k < n, (acc (k + 1)).status = 0) :
    Sound up (acc n) (initial + ∑ k ∈ Finset.range n, x k) := by
  induction n with
  | zero => simpa using hInitial
  | succ n ih =>
    have hlt : ∀ k < n, k < n + 1 := fun k hk => Nat.lt_succ_of_lt hk
    have ha := ih (fun k hk => hTerm k (hlt k hk))
      (fun k hk => hStep k (hlt k hk))
      (fun k hk => hAccepted k (hlt k hk))
    have hs : (add up (acc n).value (term n).value).status = 0 := by
      rw [← hStep n (Nat.lt_succ_self n)]
      exact hAccepted n (Nat.lt_succ_self n)
    rw [hStep n (Nat.lt_succ_self n), Finset.sum_range_succ, ← add_assoc]
    exact add_sound up (acc n) (term n) _ _ ha (hTerm n (Nat.lt_succ_self n)) hs

theorem residual_sound (up : Bool) (initialBound finalBound boundaryBound : Checked)
    (initial final boundary residual : ℝ)
    (hBalance : final - initial = boundary + residual)
    (hInitial : Sound (!up) initialBound initial)
    (hFinal : Sound up finalBound final)
    (hBoundary : Sound (!up) boundaryBound boundary)
    (hDelta : (sub up finalBound.value initialBound.value).status = 0)
    (hResidual : (sub up (sub up finalBound.value initialBound.value).value
      boundaryBound.value).status = 0) :
    Sound up (sub up (sub up finalBound.value initialBound.value).value
      boundaryBound.value) residual := by
  have h := sub_sound up (sub up finalBound.value initialBound.value)
    boundaryBound (final - initial) boundary
    (sub_sound up finalBound initialBound final initial hFinal hInitial hDelta)
    hBoundary hResidual
  simpa only [hBalance, add_sub_cancel_left] using h

#print axioms add_sound
#print axioms sub_sound
#print axioms sum_range_sound
#print axioms residual_sound
end Project.ProofKit.F64Outward
