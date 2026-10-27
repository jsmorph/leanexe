import Verified.BoundFacts
import Verified.LoopCostLast
import LeanExe.Dialect.Loop
import LeanExe.Dialect.RepeatWhile
import Verified.Bytes.Allocation

/-! Facts for bounding the generated allocation bounds of programs: the allocation cost of byte
strings, the sizes of arrays that loops extend once per pass, and the result of a loop that counts
down while its condition holds. -/

namespace Verified

theorem allocationCost_le (count : Nat) : Bytes.allocationCost count ≤ count + 55 := by
  unfold Bytes.allocationCost
  split
  · omega
  · rw [Nat.max_def]
    split <;> omega

theorem allocationCost_mono {small large : Nat} (le : small ≤ large) :
    Bytes.allocationCost small ≤ Bytes.allocationCost large := by
  unfold Bytes.allocationCost
  split
  · omega
  · split
    · omega
    · rw [Nat.max_def, Nat.max_def]
      split <;> split <;> omega

theorem fold_push_size {α β : Type} {F : UInt64 → Array α × β → Array α × β}
    (pushes : ∀ i state, (F i state).1.size = state.1.size + 1) (init : Array α × β) :
    ∀ count : Nat,
      (Nat.fold count (fun i _ state => F (UInt64.ofNat i) state) init).1.size =
        init.1.size + count
  | 0 => by simp
  | count + 1 => by
      simp only [Nat.fold_succ, pushes, fold_push_size pushes init count]
      omega

theorem loop_push_size {α β : Type} {F : UInt64 → Array α × β → Array α × β}
    (pushes : ∀ i state, (F i state).1.size = state.1.size + 1) (count : UInt64)
    (init : Array α × β) : (LeanExe.loop count init F).1.size = init.1.size + count.toNat :=
  fold_push_size pushes init count.toNat

theorem repeatWhile_pred_le (fuel start : UInt64) (cond : UInt64 → Bool)
    (positive : ∀ size, cond size = true → 0 < size.toNat) :
    (LeanExe.repeatWhile fuel start cond (fun size => size - 1)).toNat ≤ start.toNat := by
  unfold LeanExe.repeatWhile
  generalize fuel.toNat = steps
  induction steps generalizing start with
  | zero => simp [LeanExe.repeatWhile.go]
  | succ steps ih =>
      simp only [LeanExe.repeatWhile.go]
      split
      · rename_i holds
        have startPositive := positive start holds
        have one : (1 : UInt64) ≤ start :=
          UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_one]; omega)
        have previous := ih (start - 1)
        rw [UInt64.toNat_sub_of_le _ _ one] at previous
        omega
      · exact Nat.le_refl _

theorem blockCost_le_of_le {small large : Nat} (le : small ≤ large) :
    blockCost small ≤ blockCost large := by
  rw [blockCost_eq, blockCost_eq]
  omega

theorem toUInt64_toNat_le (n : Nat) : n.toUInt64.toNat ≤ n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.mod_le _ _

theorem ite_zero_le (condition : Prop) [Decidable condition] (x : Nat) :
    (if condition then x else 0) ≤ x := by
  split <;> omega

theorem ite_push_size_le {α : Type} (condition : Prop) [Decidable condition] (xs : Array α)
    (x : α) : (if condition then xs.push x else xs).size ≤ xs.size + 1 := by
  split <;> simp

/-- `loopCost_le` with the cost and the step needed only at the indices of the loop's passes. -/
theorem loopCost_le_upto {α : Type} {CA : α → Nat} {C : α → Bool} {BA : UInt64 → α → Nat}
    {F : UInt64 → α → α} (P : Nat → α → Prop) (cost : Nat → Nat) (n : Nat)
    (hcost : ∀ k s, k < n → P k s → CA s + (if C s then BA (UInt64.ofNat k) s else 0) ≤ cost k)
    (hstep : ∀ k s, k < n → P k s → C s = true → P (k + 1) (F (UInt64.ofNat k) s)) {I : α}
    (hI : P 0 I) : loopCost CA C BA F n 0 I ≤ sumBelow cost n := by
  suffices h : ∀ m k s, k + m = n → P k s →
      loopCost CA C BA F m (UInt64.ofNat k) s ≤ sumBelow (fun j => cost (k + j)) m by
    simpa using h n 0 I (by omega) hI
  intro m
  induction m with
  | zero => intro _ _ _ _; simp [loopCost, sumBelow]
  | succ m ih =>
    intro k s hkm hP
    have hc := hcost k s (by omega) hP
    rw [sumBelow_succ']
    cases hC : C s
    · simp only [loopCost, hC, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hc ⊢
      omega
    · simp only [loopCost, hC, ↓reduceIte, Nat.add_zero] at hc ⊢
      have hk : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
        omega
      have hn := ih (k + 1) _ (by omega) (hstep k s (by omega) hP hC)
      rw [← hk] at hn
      have hsum : sumBelow (fun j => cost (k + 1 + j)) m =
          sumBelow (fun j => cost (k + (j + 1))) m := by
        congr 1; funext j; congr 1; omega
      omega

theorem ofNat_succ (k : Nat) : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat]
  omega

/-- A loop that counts up from `k` while its condition holds stops at `k` or above. -/
theorem repeatWhile_count_ge (C : UInt64 → Bool) :
    ∀ (fuel k : Nat), k + fuel < UInt64.size →
      k ≤ (LeanExe.repeatWhile.go C (fun i => i + 1) fuel (UInt64.ofNat k)).toNat
  | 0, k, small => by
      simp only [LeanExe.repeatWhile.go, UInt64.toNat_ofNat_of_lt' (show k < UInt64.size by omega)]
      exact Nat.le_refl k
  | fuel + 1, k, small => by
      simp only [LeanExe.repeatWhile.go]
      split
      · rw [ofNat_succ]
        have := repeatWhile_count_ge C fuel (k + 1) (by omega)
        omega
      · rw [UInt64.toNat_ofNat_of_lt' (show k < UInt64.size by omega)]

/-- A loop that counts up while its condition holds only below `B` stops at `B` or below. -/
theorem repeatWhile_count_le (C : UInt64 → Bool) (B : Nat) (bound : B < UInt64.size)
    (below : ∀ k, C k = true → k.toNat < B) :
    ∀ (fuel : Nat) (s : UInt64), s.toNat ≤ B →
      (LeanExe.repeatWhile.go C (fun i => i + 1) fuel s).toNat ≤ B
  | 0, _, le => le
  | fuel + 1, s, le => by
      have usize : UInt64.size = 18446744073709551616 := rfl
      simp only [LeanExe.repeatWhile.go]
      split
      · rename_i holds
        have lt := below s holds
        apply repeatWhile_count_le C B bound below fuel
        rw [UInt64.toNat_add, UInt64.toNat_one]
        omega
      · exact le

/-- The charge of a loop that counts up from `k` and charges only its condition: at most `c` for
each count from `k` to the count where the loop stops. -/
theorem loopCost_count_le (CA : UInt64 → Nat) (C : UInt64 → Bool) (c : Nat) :
    ∀ (fuel k : Nat) (i : UInt64), k + fuel < UInt64.size →
      (∀ j, k ≤ j → j ≤ (LeanExe.repeatWhile.go C (fun i => i + 1) fuel (UInt64.ofNat k)).toNat →
        CA (UInt64.ofNat j) ≤ c) →
      loopCost CA C (fun _ _ => 0) (fun _ s => s + 1) fuel i (UInt64.ofNat k) + k * c ≤
        ((LeanExe.repeatWhile.go C (fun i => i + 1) fuel (UInt64.ofNat k)).toNat + 1) * c
  | 0, k, _, small, _ => by
      simp only [loopCost, LeanExe.repeatWhile.go,
        UInt64.toNat_ofNat_of_lt' (show k < UInt64.size by omega), Nat.add_mul, Nat.one_mul]
      omega
  | fuel + 1, k, i, small, hcost => by
      have kNat := UInt64.toNat_ofNat_of_lt' (show k < UInt64.size by omega)
      have ge := repeatWhile_count_ge C fuel (k + 1) (by omega)
      cases hC : C (UInt64.ofNat k)
      · have here := hcost k (Nat.le_refl k) (by
          simp only [LeanExe.repeatWhile.go, hC, Bool.false_eq_true, ↓reduceIte, kNat]
          exact Nat.le_refl k)
        simp only [loopCost, LeanExe.repeatWhile.go, hC, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero, kNat, Nat.add_mul, Nat.one_mul]
        omega
      · have shift : ∀ j, j ≤ (LeanExe.repeatWhile.go C (fun i => i + 1) fuel
            (UInt64.ofNat (k + 1))).toNat →
            j ≤ (LeanExe.repeatWhile.go C (fun i => i + 1) (fuel + 1) (UInt64.ofNat k)).toNat := by
          intro j hj
          simp only [LeanExe.repeatWhile.go, hC, ↓reduceIte, ofNat_succ]
          exact hj
        have rest := loopCost_count_le CA C c fuel (k + 1) (i + 1) (by omega)
          (fun j lo hi => hcost j (by omega) (shift j hi))
        have here := hcost k (Nat.le_refl k) (shift k (by omega))
        simp only [loopCost, LeanExe.repeatWhile.go, hC, ↓reduceIte, Nat.zero_add, ofNat_succ]
        rw [Nat.add_mul k 1 c, Nat.one_mul] at rest
        omega

/-- The charge of a loop that counts up from 0 and charges only its condition: at most `c` for
each count up to the result of the matching `LeanExe.repeatWhile`. -/
theorem loopCost_repeatWhile_le (CA : UInt64 → Nat) (C : UInt64 → Bool) (c : Nat) (fuel : UInt64)
    (hcost : ∀ j, j ≤ (LeanExe.repeatWhile fuel 0 C (fun i => i + 1)).toNat →
      CA (UInt64.ofNat j) ≤ c) :
    loopCost CA C (fun _ _ => 0) (fun _ s => s + 1) fuel.toNat 0 0 ≤
      ((LeanExe.repeatWhile fuel 0 C (fun i => i + 1)).toNat + 1) * c := by
  have bound := loopCost_count_le CA C c fuel.toNat 0 0
    (by have := fuel.toNat_lt_size; omega) (fun j _ hi => hcost j hi)
  rw [Nat.zero_mul, Nat.add_zero] at bound
  exact bound

end Verified
