import Library.Sorting.Shellsort.Program
import Library.Sorting.Shellsort.Spec
import Library.Sorting.StraightInsertion.Proof
import Library.Sorting.Heapsort.Proof
import Library.Sorting.Sorted
import LeanExe.Dialect.Lemmas

/-! The proof that `shellsort` returns the array's elements in nondecreasing order.  Every pass with
an increment above 1 permutes the array, since each move of `insertBy` is an exchange of the word
`v` with the word `h` places before it in the array that holds `v` at the vacant position, and
straight insertion sorts every array, so the result is the unique sorted permutation. -/

namespace Library.Sorting.Shellsort

open LeanExe.Dialect
open Library.Sorting.Heapsort (swap swap_perm)
open Library.Sorting.StraightInsertion (straightInsertion straightInsertion_sorted_perm)

theorem set!_self (a : Array UInt64) (i : Nat) (hi : i < a.size) : a.set! i a[i]! = a := by
  rw [getElem!_pos a i hi]
  simp [Array.setIfInBounds, hi]

/-- One move of step D5 is an exchange in the array that holds `v` at the vacant position. -/
theorem move_eq (xs : Array UInt64) (v : UInt64) (i j : Nat) (hi : i < xs.size)
    (hj : j < xs.size) (hij : i ≠ j) (hsize : xs.size < 2 ^ 64) :
    (xs.set! i xs[j]!).set! j v =
      swap (UInt64.ofNat i) (UInt64.ofNat j) (xs.set! i v) := by
  have hi64 : (UInt64.ofNat i).toNat = i := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hj64 : (UInt64.ofNat j).toNat = j := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  unfold swap
  simp only [hi64, hj64]
  rw [Array.getElem!_set!_self _ _ _ hi, Array.getElem!_set!_ne _ _ _ _ hij]
  simp

/-- `insertBy v h i xs` has the size of `xs` and is a permutation of `xs.set! i v`. -/
theorem insertBy_perm (v h : UInt64) :
    ∀ (n : Nat) (i : UInt64) (xs : Array UInt64), i.toNat = n → i.toNat < xs.size →
      xs.size < 2 ^ 64 →
      (insertBy v h i xs).size = xs.size ∧
        (insertBy v h i xs).toList.Perm (xs.set! i.toNat v).toList := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i xs hn hi hsize
    rw [insertBy]
    by_cases h0 : 0 < h
    · rw [ite_eq_left h0]
      by_cases hle : h ≤ i
      · rw [ite_eq_left hle]
        have hsub : (i - h).toNat = i.toNat - h.toNat := UInt64.toNat_sub_of_le _ _ hle
        have hlt : (i - h).toNat < i.toNat := by
          rw [UInt64.lt_iff_toNat_lt] at h0; rw [UInt64.le_iff_toNat_le] at hle
          simp only [UInt64.reduceToNat] at h0
          omega
        by_cases hv : v < xs[(i - h).toNat]!
        · rw [ite_eq_left hv]
          have hsz : (i - h).toNat < (xs.set! i.toNat xs[(i - h).toNat]!).size := by
            rw [Array.size_set!]; omega
          obtain ⟨h1, h2⟩ := ih (i - h).toNat (by omega) (i - h) _ rfl hsz
            (by rw [Array.size_set!]; exact hsize)
          refine ⟨by rw [h1, Array.size_set!], h2.trans ?_⟩
          have hne : i.toNat ≠ (i - h).toNat := by omega
          rw [move_eq xs v i.toNat (i - h).toNat hi (by omega) hne hsize]
          exact swap_perm _ _ _ (by simp; omega) (by simp; omega)
        · rw [ite_eq_right hv]
          exact ⟨Array.size_set! .., List.Perm.refl _⟩
      · rw [ite_eq_right hle]
        exact ⟨Array.size_set! .., List.Perm.refl _⟩
    · rw [ite_eq_right h0]
      exact ⟨Array.size_set! .., List.Perm.refl _⟩

theorem pass_perm (h : UInt64) (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    (pass h xs).size = xs.size ∧ (pass h xs).toList.Perm xs.toList := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  unfold pass
  simp only
  split
  · rename_i hh
    have hn := UInt64.lt_iff_toNat_lt.mp hh
    rw [hN] at hn
    have hcount : (xs.size.toUInt64 - h).toNat = xs.size - h.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt hh), hN]
    refine loop_induction
      (P := fun (_ : Nat) (acc : Array UInt64) => acc.size = xs.size ∧ acc.toList.Perm xs.toList)
      ⟨rfl, List.Perm.refl _⟩ ?_
    intro k acc hk ⟨hs, hp⟩
    rw [hcount] at hk
    have hj : (h + UInt64.ofNat k).toNat = h.toNat + k := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      have := UInt64.toNat_lt h
      omega
    have hjs : (h + UInt64.ofNat k).toNat < acc.size := by rw [hj, hs]; omega
    obtain ⟨p1, p2⟩ := insertBy_perm acc[(h + UInt64.ofNat k).toNat]! h _
      (h + UInt64.ofNat k) acc rfl hjs (by rw [hs]; exact hsize)
    rw [set!_self acc _ hjs] at p2
    exact ⟨p1.trans hs, p2.trans hp⟩
  · exact ⟨rfl, List.Perm.refl _⟩

theorem passes_perm (h : UInt64) (xs : Array UInt64) :
    xs.size < 2 ^ 64 → (passes h xs).size = xs.size ∧ (passes h xs).toList.Perm xs.toList := by
  fun_induction passes h xs with
  | case1 h xs _ ih =>
    intro hsize
    obtain ⟨p1, p2⟩ := pass_perm h xs hsize
    obtain ⟨q1, q2⟩ := ih (by rw [p1]; exact hsize)
    exact ⟨q1.trans p1, q2.trans p2⟩
  | case2 => exact fun _ => ⟨rfl, List.Perm.refl _⟩

theorem shellsort_eq (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    shellsort xs = expected xs := by
  have h := passes_perm (firstIncrement xs.size.toUInt64 1) xs hsize
  obtain ⟨hs, hp⟩ := straightInsertion_sorted_perm (passes (firstIncrement xs.size.toUInt64 1) xs)
    (by rw [h.1]; exact hsize)
  show straightInsertion (passes (firstIncrement xs.size.toUInt64 1) xs) = expected xs
  unfold expected
  rw [← Library.Sorting.eq_mergeSort_of_sorted_perm hs (hp.trans h.2), Array.toArray_toList]

end Library.Sorting.Shellsort
