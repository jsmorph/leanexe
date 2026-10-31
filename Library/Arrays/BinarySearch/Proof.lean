import Library.Arrays.BinarySearch.Program
import Library.Arrays.BinarySearch.Spec

/-! The proof that binary search on a sorted array returns `expected`, the number of elements less
than the key.  `search_spec` states the search's invariant: every element before `lo` is less than
the key, and every element from `hi` on is at least the key.  The result therefore splits the array
into the elements less than the key and the others, and `lowerBound_eq` counts the first part. -/

namespace Library.Arrays.BinarySearch

theorem search_of_lt {xs : Array UInt64} {key lo hi : UInt64} (h : lo < hi) :
    search xs key lo hi =
      if xs[(lo + (hi - lo) / 2).toNat]! < key then search xs key (lo + (hi - lo) / 2 + 1) hi
      else search xs key lo (lo + (hi - lo) / 2) := by
  rw [search, ite_eq_left h]

theorem search_of_not_lt {xs : Array UInt64} {key lo hi : UInt64} (h : ¬ lo < hi) :
    search xs key lo hi = lo := by
  rw [search, ite_eq_right h]

theorem mid_toNat {lo hi : UInt64} (h : lo < hi) :
    (lo + (hi - lo) / 2).toNat = lo.toNat + (hi.toNat - lo.toNat) / 2 := by
  have := UInt64.toNat_lt hi
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_div, UInt64.reduceToNat]
  omega

theorem succ_toNat {m hi : UInt64} (h : m < hi) : (m + 1).toNat = m.toNat + 1 := by
  have := UInt64.toNat_lt hi
  simp only [UInt64.lt_iff_toNat_lt] at h
  simp only [UInt64.toNat_add, UInt64.reduceToNat]
  omega

/-- The invariant of the search: from a range `[lo, hi)` of a sorted array with every element
before `lo` less than the key and every element from `hi` on at least the key, the result lies in
the array, every element before it is less than the key, and every element from it on is at least
the key. -/
theorem search_spec (xs : Array UInt64) (key : UInt64) (hs : Sorted xs) (lo hi : UInt64)
    (hle : lo ≤ hi) (hhi : hi.toNat ≤ xs.size)
    (hbelow : ∀ j, j < lo.toNat → xs[j]! < key)
    (habove : ∀ j, hi.toNat ≤ j → j < xs.size → key ≤ xs[j]!) :
    (search xs key lo hi).toNat ≤ xs.size ∧
      (∀ j, j < (search xs key lo hi).toNat → xs[j]! < key) ∧
      (∀ j, (search xs key lo hi).toNat ≤ j → j < xs.size → key ≤ xs[j]!) := by
  have hle' := UInt64.le_iff_toNat_le.mp hle
  by_cases hlt : lo < hi
  · rw [search_of_lt hlt]
    have hm := mid_toNat hlt
    have hlo := UInt64.lt_iff_toNat_lt.mp hlt
    have hmhi : lo + (hi - lo) / 2 < hi := by
      rw [UInt64.lt_iff_toNat_lt, hm]; omega
    have hs1 := succ_toNat hmhi
    by_cases hk : xs[(lo + (hi - lo) / 2).toNat]! < key
    · rw [ite_eq_left hk]
      refine search_spec xs key hs _ hi
        (by rw [UInt64.le_iff_toNat_le, hs1, hm]; omega) hhi ?_ habove
      intro j hj
      rw [hs1, hm] at hj
      have hx := UInt64.le_iff_toNat_le.mp (hs j (lo + (hi - lo) / 2).toNat (by rw [hm]; omega) (by rw [hm]; omega))
      have hk' := UInt64.lt_iff_toNat_lt.mp hk
      exact UInt64.lt_iff_toNat_lt.mpr (by omega)
    · rw [ite_eq_right hk]
      refine search_spec xs key hs lo _
        (by rw [UInt64.le_iff_toNat_le, hm]; omega) (by rw [hm]; omega) hbelow ?_
      intro j hj hjs
      have hx := UInt64.le_iff_toNat_le.mp (hs _ j hj hjs)
      have hk' : ¬ (xs[(lo + (hi - lo) / 2).toNat]!).toNat < key.toNat := by
        rwa [← UInt64.lt_iff_toNat_lt]
      exact UInt64.le_iff_toNat_le.mpr (by omega)
  · rw [search_of_not_lt hlt]
    have heq : lo = hi := by
      have : ¬ lo.toNat < hi.toNat := fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
      exact UInt64.toNat_inj.mp (by omega)
    subst heq
    exact ⟨hhi, hbelow, habove⟩
termination_by (hi - lo).toNat
decreasing_by
  all_goals
    have := UInt64.toNat_lt lo
    have := UInt64.toNat_lt hi
    simp only [UInt64.lt_iff_toNat_lt] at hlt
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_div, UInt64.reduceToNat]
    omega

/-- On a sorted array, `lowerBound` returns an index of the array, at or after every element less
than the key and at or before every element at least the key. -/
theorem lowerBound_spec (xs : Array UInt64) (key : UInt64) (hs : Sorted xs)
    (hsize : xs.size < 2 ^ 64) :
    (lowerBound xs key).toNat ≤ xs.size ∧
      (∀ j, j < (lowerBound xs key).toNat → xs[j]! < key) ∧
      (∀ j, (lowerBound xs key).toNat ≤ j → j < xs.size → key ≤ xs[j]!) := by
  have hn : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  exact search_spec xs key hs 0 xs.size.toUInt64 (UInt64.le_iff_toNat_le.mpr (by simp))
    (Nat.le_of_eq hn) (fun j hj => absurd hj (by simp)) (fun j hj hjs => absurd hjs (by omega))

/-- A list whose first `r` elements satisfy `p` and whose other elements do not has `r` elements
that satisfy `p`. -/
theorem countP_of_split (l : List UInt64) (p : UInt64 → Bool) (r : Nat) (hr : r ≤ l.length)
    (hin : ∀ j (h : j < l.length), j < r → p l[j] = true)
    (hout : ∀ j (h : j < l.length), r ≤ j → p l[j] = false) :
    l.countP p = r := by
  rw [← List.take_append_drop r l, List.countP_append]
  have h1 : (l.take r).countP p = r := by
    rw [List.countP_eq_length.mpr]
    · simp [hr]
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      simp only [List.length_take] at hi
      rw [List.getElem_take]
      exact hin i (by omega) (by omega)
  have h2 : (l.drop r).countP p = 0 := by
    rw [List.countP_eq_zero]
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    simp only [List.length_drop] at hi
    rw [List.getElem_drop]
    simp [hout (r + i) (by omega) (by omega)]
  omega

/-- Binary search on a sorted array computes the specification: the number of elements less than
the key. -/
theorem lowerBound_eq (xs : Array UInt64) (key : UInt64) (hs : Sorted xs)
    (hsize : xs.size < 2 ^ 64) : lowerBound xs key = expected (xs, key) := by
  obtain ⟨hr, hin, hout⟩ := lowerBound_spec xs key hs hsize
  unfold expected
  rw [countP_of_split xs.toList (fun y => decide (y < key)) (lowerBound xs key).toNat
    (by simpa using hr)]
  · exact UInt64.ofNat_toNat.symm
  · intro j hj hjr
    have := hin j hjr
    simp only [Array.length_toList] at hj
    simp only [Array.getElem_toList, decide_eq_true_eq]
    rwa [getElem!_pos xs j hj] at this
  · intro j hj hjr
    have := hout j hjr (by simpa using hj)
    simp only [Array.length_toList] at hj
    simp only [Array.getElem_toList, decide_eq_false_iff_not]
    rw [getElem!_pos xs j hj] at this
    exact fun h => absurd (UInt64.lt_iff_toNat_lt.mp h) (Nat.not_lt.mpr
      (UInt64.le_iff_toNat_le.mp this))

end Library.Arrays.BinarySearch
