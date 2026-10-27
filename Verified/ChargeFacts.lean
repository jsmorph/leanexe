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

end Verified
