/-! The uniqueness of a sorted permutation of words, which the sorting modules use to show that a
program's result equals `List.mergeSort` of its input. -/

namespace Library.Sorting

/-- `List.mergeSort` with the unsigned order of words returns a list in nondecreasing order. -/
theorem pairwise_mergeSort_le (m : List UInt64) :
    (m.mergeSort fun a b => a ≤ b).Pairwise (· ≤ ·) := by
  have hms := List.pairwise_mergeSort (le := fun a b : UInt64 => decide (a ≤ b))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq, UInt64.le_iff_toNat_le] at *; omega)
    (fun a b => by
      rcases Nat.le_total a.toNat b.toNat with h | h <;>
        simp [UInt64.le_iff_toNat_le, h]) m
  exact hms.imp fun h => by simpa using h

/-- A list of words in nondecreasing order that is a permutation of `m` is `m` sorted by
`List.mergeSort`. -/
theorem eq_mergeSort_of_sorted_perm {l m : List UInt64} (hs : l.Pairwise (· ≤ ·))
    (hp : l.Perm m) : l = m.mergeSort fun a b => a ≤ b :=
  List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun _ _ _ _ hab hba => UInt64.toNat_inj.mp
      (Nat.le_antisymm (UInt64.le_iff_toNat_le.mp hab) (UInt64.le_iff_toNat_le.mp hba)))
    hs (pairwise_mergeSort_le m) (hp.trans (List.mergeSort_perm _ _).symm)

end Library.Sorting
