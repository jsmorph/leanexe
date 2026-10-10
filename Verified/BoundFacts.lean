import Verified.Bound

/-! Facts about the allocation bound for proofs that use it: names for the blocks that it charges,
with their sizes in bytes, and the sums of `sumBelow` and `loopCost`.  `loopCost_le` bounds the
cost of a loop by an invariant on its index and state. -/

namespace Verified

/-- The growth of `top` for a block of `words` words after its length word. -/
def blockCost (words : Nat) : Nat := allocCost ((words + 1) * 8)

/-- The growth of `top` for the block into which an owned array of `words` words grows. -/
def growCost (words : Nat) : Nat := allocCost (16 * (words + 1))

theorem blockCost_eq (words : Nat) : blockCost words = 8 * words + 56 := by
  simp only [blockCost, allocCost]; omega

theorem growCost_eq (words : Nat) : growCost words = 16 * words + 64 := by
  simp only [growCost, allocCost]; omega

theorem sumBelow_zero : ∀ n : Nat, sumBelow (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by simp only [sumBelow, sumBelow_zero n]

theorem sumBelow_const (c : Nat) : ∀ n : Nat, sumBelow (fun _ => c) n = n * c
  | 0 => by simp [sumBelow]
  | n + 1 => by rw [sumBelow, sumBelow_const c n, Nat.succ_mul]

theorem sumBelow_le {f g : Nat → Nat} : ∀ {n : Nat}, (∀ k, k < n → f k ≤ g k) →
    sumBelow f n ≤ sumBelow g n
  | 0, _ => Nat.le_refl _
  | n + 1, h => by
    have := sumBelow_le (n := n) fun k hk => h k (by omega)
    have := h n (by omega)
    simp only [sumBelow]
    omega

/-- `sumBelow` from its first term. -/
theorem sumBelow_succ' (f : Nat → Nat) :
    ∀ n : Nat, sumBelow f (n + 1) = f 0 + sumBelow (fun k => f (k + 1)) n
  | 0 => by simp [sumBelow]
  | n + 1 => by
    have ih := sumBelow_succ' f n
    simp only [sumBelow] at ih ⊢
    omega

theorem loopCost_eq_zero {α : Type} (C : α → Bool) (F : UInt64 → α → α) :
    ∀ (n : Nat) (i : UInt64) (s : α), loopCost (fun _ => 0) C (fun _ _ => 0) F n i s = 0
  | 0, _, _ => rfl
  | n + 1, i, s => by
    simp only [loopCost, loopCost_eq_zero C F n, Nat.zero_add, ite_self]

/-- A bound on the cost of a loop from an invariant `P` of its index and state: when each state
that `P` admits at index `k` costs at most `cost k`, through the condition and, when the condition
holds, the body, and the step keeps `P`, the loop costs at most the sum of `cost`. -/
theorem loopCost_le {α : Type} {CA : α → Nat} {C : α → Bool} {BA : UInt64 → α → Nat}
    {F : UInt64 → α → α} (P : Nat → α → Prop) (cost : Nat → Nat)
    (hcost : ∀ k s, P k s → CA s + (if C s then BA (UInt64.ofNat k) s else 0) ≤ cost k)
    (hstep : ∀ k s, P k s → C s = true → P (k + 1) (F (UInt64.ofNat k) s)) {n : Nat} {I : α}
    (hI : P 0 I) : loopCost CA C BA F n 0 I ≤ sumBelow cost n := by
  suffices h : ∀ n k s, P k s →
      loopCost CA C BA F n (UInt64.ofNat k) s ≤ sumBelow (fun j => cost (k + j)) n by
    simpa using h n 0 I hI
  intro n
  induction n with
  | zero => intro _ _ _; simp [loopCost, sumBelow]
  | succ n ih =>
    intro k s hP
    have hc := hcost k s hP
    rw [sumBelow_succ']
    cases hC : C s
    · simp only [loopCost, hC, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc ⊢
      omega
    · simp only [loopCost, hC, ↓reduceIte, Nat.add_zero] at hc ⊢
      have hk : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
        omega
      have hn := ih (k + 1) _ (hstep k s hP hC)
      rw [← hk] at hn
      have hsum : sumBelow (fun j => cost (k + 1 + j)) n =
          sumBelow (fun j => cost (k + (j + 1))) n := by
        congr 1; funext j; congr 1; omega
      omega

end Verified
