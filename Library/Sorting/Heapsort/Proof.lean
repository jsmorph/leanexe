import Library.Sorting.Heapsort.Program
import Library.Sorting.Heapsort.Spec
import LeanExe.Dialect.Lemmas

/-! The proof that heapsort returns the array's elements in nondecreasing order.  Every step of
the program exchanges two elements, so the result is a permutation of the input
(`siftDown_perm`, `heapify_spec`, `heapsort_sorted_perm`).  `HeapFrom a n L` states the heap order
on `a[0, n)` for every node at or after `L`.  `siftDown_spec` states the invariant of the sift: the
heap order holds at every node at or after `L` except the moving node `i`, and the children of `i`
are at most its parent.  `heapify` establishes the heap order on the whole array, and each step of
`heapsort` keeps a heap on a prefix, a sorted suffix, and every element of the prefix at most every
element of the suffix.  A sorted permutation is unique, so the result equals `expected`. -/

namespace Library.Sorting.Heapsort

open LeanExe.Dialect

/-! ### The order of words -/

theorem wle_trans {a b c : UInt64} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  UInt64.le_iff_toNat_le.mpr
    (Nat.le_trans (UInt64.le_iff_toNat_le.mp h1) (UInt64.le_iff_toNat_le.mp h2))

theorem wle_of_lt {a b : UInt64} (h : a < b) : a ≤ b :=
  UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp h))

theorem wle_of_not_lt {a b : UInt64} (h : ¬ a < b) : b ≤ a :=
  UInt64.le_iff_toNat_le.mpr (Nat.le_of_not_lt fun h' => h (UInt64.lt_iff_toNat_lt.mpr h'))

theorem wle_refl (a : UInt64) : a ≤ a := UInt64.le_iff_toNat_le.mpr (Nat.le_refl _)

theorem wle_antisymm {a b : UInt64} (h1 : a ≤ b) (h2 : b ≤ a) : a = b :=
  UInt64.toNat_inj.mp
    (Nat.le_antisymm (UInt64.le_iff_toNat_le.mp h1) (UInt64.le_iff_toNat_le.mp h2))

theorem wle_total (a b : UInt64) : a ≤ b ∨ b ≤ a := by
  rcases Nat.le_total a.toNat b.toNat with h | h
  · exact Or.inl (UInt64.le_iff_toNat_le.mpr h)
  · exact Or.inr (UInt64.le_iff_toNat_le.mpr h)

/-! ### Exchanges -/

theorem swap_size (xs : Array UInt64) (i j : UInt64) : (swap i j xs).size = xs.size := by
  simp [swap]

theorem swap_get (xs : Array UInt64) (i j : UInt64) (hi : i.toNat < xs.size)
    (hj : j.toNat < xs.size) (k : Nat) :
    (swap i j xs)[k]! =
      if k = j.toNat then xs[i.toNat]! else if k = i.toNat then xs[j.toNat]! else xs[k]! := by
  unfold swap
  simp only [Array.set!_eq_setIfInBounds]
  by_cases hk : k < xs.size
  · rw [getElem!_pos _ k (by simpa using hk), Array.getElem_setIfInBounds (by simpa using hk),
      Array.getElem_setIfInBounds hk, getElem!_pos xs k hk]
    by_cases h1 : k = j.toNat <;> by_cases h2 : k = i.toNat <;> simp_all [eq_comm]
  · rw [getElem!_neg _ k (by simpa using hk), getElem!_neg xs k hk]
    have h1 : k ≠ j.toNat := by omega
    have h2 : k ≠ i.toNat := by omega
    simp [h1, h2]

theorem swap_perm (xs : Array UInt64) (i j : UInt64) (hi : i.toNat < xs.size)
    (hj : j.toNat < xs.size) : (swap i j xs).toList.Perm xs.toList := by
  have h := Array.swap_perm hi hj
  rw [Array.perm_iff_toList_perm, Array.toList_swap] at h
  unfold swap
  rw [Array.toList_set!, Array.toList_set!, getElem!_pos xs i.toNat hi, getElem!_pos xs j.toNat hj]
  exact h

/-! ### The larger child -/

/-- The child of node `i` of the heap `xs[0, n)` with the larger word: `2i + 2` when that child
exists and holds a larger word than `2i + 1`, and `2i + 1` otherwise.  The callers have `i < n / 2`. -/
def maxChild (xs : Array UInt64) (i n : UInt64) : UInt64 :=
  if i + i + 2 < n ∧ xs[(i + i + 1).toNat]! < xs[(i + i + 2).toNat]! then i + i + 2 else i + i + 1

theorem maxChild_bounds (xs : Array UInt64) {i n : UInt64} (h : i < n / 2) :
    i < maxChild xs i n ∧ maxChild xs i n < n := by
  have hn := UInt64.toNat_lt n
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div] at h
  simp only [UInt64.reduceToNat] at h
  unfold maxChild
  split
  · rename_i hc
    have hc' := UInt64.lt_iff_toNat_lt.mp hc.1
    simp only [UInt64.toNat_add, UInt64.reduceToNat] at hc'
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.reduceToNat]
    omega

theorem maxChild_spec (a : Array UInt64) {i n : UInt64} (h : i.toNat < n.toNat / 2) :
    ((maxChild a i n).toNat = 2 * i.toNat + 1 ∨ (maxChild a i n).toNat = 2 * i.toNat + 2) ∧
      (maxChild a i n).toNat < n.toNat ∧
      a[2 * i.toNat + 1]! ≤ a[(maxChild a i n).toNat]! ∧
      (2 * i.toNat + 2 < n.toNat → a[2 * i.toNat + 2]! ≤ a[(maxChild a i n).toNat]!) := by
  have hn := UInt64.toNat_lt n
  have h1 : (i + i + 1).toNat = 2 * i.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  have h2 : (i + i + 2).toNat = 2 * i.toNat + 2 := by
    simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega
  unfold maxChild
  split
  · rename_i hc
    rw [h1, h2] at hc
    rw [h2]
    have h3 := UInt64.lt_iff_toNat_lt.mp hc.1
    rw [h2] at h3
    exact ⟨Or.inr rfl, h3, wle_of_lt hc.2, fun _ => wle_refl _⟩
  · rename_i hc
    rw [h1, h2] at hc
    rw [h1]
    refine ⟨Or.inl rfl, by omega, wle_refl _, fun h3 => wle_of_not_lt fun h4 => hc ⟨?_, h4⟩⟩
    rw [UInt64.lt_iff_toNat_lt, h2]; exact h3

/-! ### Sifting -/

/-- The heap order on `a[0, n)` at every node at or after `L`: each element whose parent is such
a node is at most its parent. -/
def HeapFrom (a : Array UInt64) (n L : Nat) : Prop :=
  ∀ j, 0 < j → j < n → L ≤ (j - 1) / 2 → a[j]! ≤ a[(j - 1) / 2]!

/-- The sift in terms of the larger child: the program's two branches move to `maxChild`. -/
theorem siftDown_eq (i n : UInt64) (a : Array UInt64) :
    siftDown i n a =
      if i < n / 2 then
        (if a[i.toNat]! < a[(maxChild a i n).toNat]! then
          siftDown (maxChild a i n) n (swap i (maxChild a i n) a)
        else a)
      else a := by
  rw [siftDown]
  by_cases h1 : i < n / 2
  · simp only [if_pos h1]
    unfold maxChild
    by_cases h2 : i + i + 2 < n ∧ a[(i + i + 1).toNat]! < a[(i + i + 2).toNat]!
    · simp only [if_pos h2]
    · simp only [if_neg h2]
  · simp only [if_neg h1]

theorem div_two_toNat {i n : UInt64} : i < n / 2 ↔ i.toNat < n.toNat / 2 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div]; rfl

/-- The sift keeps the size, permutes the elements, leaves the elements at `n` and beyond, and
keeps every bound on the elements of `a[0, n)`. -/
theorem siftDown_frame (n x : UInt64) (i : UInt64) (a : Array UInt64) (hn : n.toNat ≤ a.size) :
    (siftDown i n a).size = a.size ∧ (siftDown i n a).toList.Perm a.toList ∧
      (∀ k, n.toNat ≤ k → (siftDown i n a)[k]! = a[k]!) ∧
      ((∀ k, k < n.toNat → a[k]! ≤ x) → ∀ k, k < n.toNat → (siftDown i n a)[k]! ≤ x) := by
  rw [siftDown_eq]
  by_cases h1 : i < n / 2
  · rw [if_pos h1]
    have hI := div_two_toNat.mp h1
    obtain ⟨hM, hMn, -, -⟩ := maxChild_spec a hI
    have hIa : i.toNat < a.size := by omega
    have hMa : (maxChild a i n).toNat < a.size := by omega
    by_cases h2 : a[i.toNat]! < a[(maxChild a i n).toNat]!
    · rw [if_pos h2]
      obtain ⟨hs, hp, ho, hb⟩ := siftDown_frame n x (maxChild a i n)
        (swap i (maxChild a i n) a) (by rw [swap_size]; exact hn)
      refine ⟨by rw [hs, swap_size], hp.trans (swap_perm a _ _ hIa hMa), fun k hk => ?_,
        fun hx => hb fun k hk => ?_⟩
      · rw [ho k hk, swap_get a _ _ hIa hMa]
        have : k ≠ (maxChild a i n).toNat := by omega
        have : k ≠ i.toNat := by omega
        simp [*]
      · rw [swap_get a _ _ hIa hMa]
        split
        · exact hx _ (by omega)
        · split
          · exact hx _ hMn
          · exact hx _ hk
    · rw [if_neg h2]
      exact ⟨rfl, List.Perm.refl _, fun _ _ => rfl, fun hx => hx⟩
  · rw [if_neg h1]
    exact ⟨rfl, List.Perm.refl _, fun _ _ => rfl, fun hx => hx⟩
termination_by (n - i).toNat
decreasing_by
  have hb := maxChild_bounds a h1
  have := UInt64.lt_iff_toNat_lt.mp hb.1
  have := UInt64.lt_iff_toNat_lt.mp hb.2
  simp only [UInt64.toNat_sub]
  have := UInt64.toNat_lt n
  omega

/-- The invariant of the sift: when the heap order holds at every node at or after `L` except the
moving node `i`, and the children of `i` are at most the parent of `i` whenever `L < i`, the sift
makes the heap order hold at every node at or after `L`. -/
theorem siftDown_spec (n : UInt64) (L : Nat) (i : UInt64) (a : Array UInt64)
    (hn : n.toNat ≤ a.size) (hL : L ≤ i.toNat)
    (hok : ∀ j, 0 < j → j < n.toNat → L ≤ (j - 1) / 2 → (j - 1) / 2 ≠ i.toNat →
      a[j]! ≤ a[(j - 1) / 2]!)
    (hbr : L < i.toNat → ∀ j, 0 < j → j < n.toNat → (j - 1) / 2 = i.toNat →
      a[j]! ≤ a[(i.toNat - 1) / 2]!) :
    HeapFrom (siftDown i n a) n.toNat L := by
  rw [siftDown_eq]
  by_cases h1 : i < n / 2
  · rw [if_pos h1]
    have hI := div_two_toNat.mp h1
    obtain ⟨hM, hMn, hc1, hc2⟩ := maxChild_spec a hI
    have hIa : i.toNat < a.size := by omega
    have hMa : (maxChild a i n).toNat < a.size := by omega
    have hMp : ((maxChild a i n).toNat - 1) / 2 = i.toNat := by omega
    by_cases h2 : a[i.toNat]! < a[(maxChild a i n).toNat]!
    · rw [if_pos h2]
      apply siftDown_spec n L (maxChild a i n) (swap i (maxChild a i n) a)
        (by rw [swap_size]; exact hn) (by omega)
      · intro j hj0 hjn hjL hjm
        rw [swap_get a _ _ hIa hMa, swap_get a _ _ hIa hMa]
        by_cases hjM : j = (maxChild a i n).toNat
        · subst hjM
          rw [if_pos rfl, hMp]
          simp only [show i.toNat ≠ (maxChild a i n).toNat by omega, if_false, if_true]
          exact wle_of_lt h2
        · rw [if_neg hjM, if_neg hjm]
          by_cases hjI : j = i.toNat
          · rw [if_pos hjI]
            have hP : (j - 1) / 2 ≠ i.toNat := by omega
            rw [if_neg hP]
            have := hbr (by omega) _ (by omega) hMn hMp
            rw [hjI] at hP ⊢
            exact this
          · rw [if_neg hjI]
            by_cases hP : (j - 1) / 2 = i.toNat
            · rw [if_pos hP]
              rcases hM with hM | hM
              · have : j = 2 * i.toNat + 2 := by omega
                subst this
                exact hc2 hjn
              · have : j = 2 * i.toNat + 1 := by omega
                subst this
                exact hc1
            · rw [if_neg hP]
              exact hok j hj0 hjn hjL hP
      · intro _ j hj0 hjn hjp
        rw [swap_get a _ _ hIa hMa, swap_get a _ _ hIa hMa, hMp]
        have h3 : j ≠ (maxChild a i n).toNat := by omega
        have h4 : j ≠ i.toNat := by omega
        have h5 : i.toNat ≠ (maxChild a i n).toNat := by omega
        simp only [h3, h4, h5, if_false, if_true]
        have := hok j hj0 hjn (by omega) (by omega)
        rwa [hjp] at this
    · rw [if_neg h2]
      intro j hj0 hjn hjL
      by_cases hP : (j - 1) / 2 = i.toNat
      · rw [hP]
        have hle := wle_of_not_lt h2
        rcases (show j = 2 * i.toNat + 1 ∨ j = 2 * i.toNat + 2 by omega) with rfl | rfl
        · exact wle_trans hc1 hle
        · exact wle_trans (hc2 hjn) hle
      · exact hok j hj0 hjn hjL hP
  · rw [if_neg h1]
    intro j hj0 hjn hjL
    by_cases hP : (j - 1) / 2 = i.toNat
    · exfalso
      exact h1 (div_two_toNat.mpr (by omega))
    · exact hok j hj0 hjn hjL hP
termination_by (n - i).toNat
decreasing_by
  have hb := maxChild_bounds a h1
  have := UInt64.lt_iff_toNat_lt.mp hb.1
  have := UInt64.lt_iff_toNat_lt.mp hb.2
  simp only [UInt64.toNat_sub]
  have := UInt64.toNat_lt n
  omega

/-- In a heap the root is the largest element. -/
theorem heap_root (a : Array UInt64) (n : Nat) (h : HeapFrom a n 0) :
    ∀ k, k < n → a[k]! ≤ a[0]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact wle_refl _
    · exact wle_trans (h k hpos hk (Nat.zero_le _)) (ih _ (by omega) (by omega))

/-! ### Building the heap -/

theorem heapify_spec (n : UInt64) (a : Array UInt64) (hn : n.toNat ≤ a.size) :
    (heapify n a).size = a.size ∧ (heapify n a).toList.Perm a.toList ∧
      HeapFrom (heapify n a) n.toNat 0 := by
  have hn2 : (n / 2).toNat = n.toNat / 2 := UInt64.toNat_div _ _
  have hn64 := UInt64.toNat_lt n
  have h := loop_induction (n := n / 2) (init := a)
    (f := fun k acc => siftDown (n / 2 - 1 - k) n acc)
    (P := fun k acc => acc.size = a.size ∧ acc.toList.Perm a.toList ∧
      HeapFrom acc n.toNat (n.toNat / 2 - k))
    ⟨rfl, List.Perm.refl _, fun j hj0 hjn hjL => by omega⟩
    (by
      intro k acc hk ⟨hs, hp, hh⟩
      rw [hn2] at hk
      have hkk : (UInt64.ofNat k).toNat = k :=
        UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
      have hi : (n / 2 - 1 - UInt64.ofNat k).toNat = n.toNat / 2 - 1 - k := by
        simp only [UInt64.toNat_sub, hn2, hkk, UInt64.reduceToNat]; omega
      obtain ⟨hs', hp', -, -⟩ := siftDown_frame n 0 (n / 2 - 1 - UInt64.ofNat k) acc (by omega)
      refine ⟨hs'.trans hs, hp'.trans hp, ?_⟩
      have := siftDown_spec n (n.toNat / 2 - 1 - k) (n / 2 - 1 - UInt64.ofNat k) acc (by omega)
        (by omega) (fun j hj0 hjn hjL hjne => hh j hj0 hjn (by omega)) (fun h => by omega)
      intro j hj0 hjn hjL
      exact this j hj0 hjn (by omega))
  rw [hn2, Nat.sub_self] at h
  exact h

/-! ### Sorting -/

/-- `heapsort` returns a sorted permutation of its input. -/
theorem heapsort_sorted_perm (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    (∀ p q, p ≤ q → q < xs.size → (heapsort xs)[p]! ≤ (heapsort xs)[q]!) ∧
      (heapsort xs).size = xs.size ∧ (heapsort xs).toList.Perm xs.toList := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [heapsort]
  by_cases h1 : xs.size.toUInt64 ≤ 1
  · rw [if_pos h1]
    have : xs.size ≤ 1 := by have := UInt64.le_iff_toNat_le.mp h1; simpa [hN] using this
    exact ⟨fun p q hpq hq => by
      have : p = q := by omega
      subst this; exact wle_refl _, rfl, List.Perm.refl _⟩
  · rw [if_neg h1]
    have hN2 : 2 ≤ xs.size := by
      have : ¬ xs.size.toUInt64.toNat ≤ 1 := fun h =>
        h1 (UInt64.le_iff_toNat_le.mpr (by simpa using h))
      omega
    obtain ⟨hs0, hp0, hh0⟩ := heapify_spec xs.size.toUInt64 xs (by omega)
    rw [hN] at hh0
    have hcount : (xs.size.toUInt64 - 1).toNat = xs.size - 1 := by
      simp only [UInt64.toNat_sub, hN, UInt64.reduceToNat]; omega
    have h := loop_induction (n := xs.size.toUInt64 - 1)
      (init := heapify xs.size.toUInt64 xs)
      (f := fun k acc => siftDown 0 (xs.size.toUInt64 - 1 - k)
        (swap 0 (xs.size.toUInt64 - 1 - k) acc))
      (P := fun k acc => acc.size = xs.size ∧ acc.toList.Perm xs.toList ∧
        HeapFrom acc (xs.size - k) 0 ∧
        (∀ p q, xs.size - k ≤ p → p ≤ q → q < xs.size → acc[p]! ≤ acc[q]!) ∧
        (∀ p q, p < xs.size - k → xs.size - k ≤ q → q < xs.size → acc[p]! ≤ acc[q]!))
      ⟨hs0, hp0, by simpa using hh0, fun p q hp hpq hq => by omega,
        fun p q hp hq hq' => by omega⟩
      (by
        intro k acc hk ⟨hs, hp, hh, hsuf, hsep⟩
        rw [hcount] at hk
        have hkk : (UInt64.ofNat k).toNat = k :=
          UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)
        have ht : (xs.size.toUInt64 - 1 - UInt64.ofNat k).toNat = xs.size - 1 - k := by
          simp only [UInt64.toNat_sub, hN, hkk, UInt64.reduceToNat]; omega
        generalize xs.size.toUInt64 - 1 - UInt64.ofNat k = t at ht ⊢
        have h0a : (0 : UInt64).toNat < acc.size := by simp; omega
        have hta : t.toNat < acc.size := by omega
        set b := swap 0 t acc with hbdef
        have hbs : b.size = xs.size := by rw [hbdef, swap_size, hs]
        have hbget := swap_get acc 0 t h0a hta
        simp only [UInt64.toNat_zero] at hbget
        obtain ⟨hcs, hcp, hco, hcb⟩ := siftDown_frame t (acc[0]!) 0 b (by omega)
        have hroot := heap_root acc (xs.size - k) hh
        have hcb' := hcb (fun p hp => by
          rw [hbget]
          split
          · exact wle_refl _
          · split
            · exact hroot _ (by omega)
            · exact hroot _ (by omega))
        have hheap := siftDown_spec t 0 0 b (by omega) (Nat.le_refl _)
          (fun j hj0 hjn _ hjp => by
            simp only [UInt64.toNat_zero] at hjp
            have h1 : j ≠ t.toNat := by omega
            have h2 : (j - 1) / 2 ≠ t.toNat := by omega
            have h3 : j ≠ 0 := by omega
            rw [hbget, hbget, if_neg h1, if_neg h3, if_neg h2, if_neg hjp]
            exact hh j hj0 (by omega) (Nat.zero_le _))
          (fun h => by simp at h)
        refine ⟨hcs.trans hbs, hcp.trans ((swap_perm acc 0 t h0a hta).trans hp), ?_, ?_, ?_⟩
        · rw [ht] at hheap
          have : xs.size - (k + 1) = xs.size - 1 - k := by omega
          rw [this]
          exact hheap
        · intro p q hp hpq hq
          rw [hco p (by omega), hco q (by omega), hbget, hbget]
          by_cases hpt : p = t.toNat
          · rw [if_pos hpt]
            by_cases hqt : q = t.toNat
            · rw [if_pos hqt]; exact wle_refl _
            · rw [if_neg hqt, if_neg (show q ≠ 0 by omega)]
              exact hsep 0 q (by omega) (by omega) hq
          · rw [if_neg hpt, if_neg (show p ≠ 0 by omega), if_neg (show q ≠ t.toNat by omega),
              if_neg (show q ≠ 0 by omega)]
            exact hsuf p q (by omega) hpq hq
        · intro p q hp hq hq'
          have hc := hcb' p (by omega)
          rw [hco q (by omega), hbget]
          by_cases hqt : q = t.toNat
          · rw [if_pos hqt]; exact hc
          · rw [if_neg hqt, if_neg (show q ≠ 0 by omega)]
            exact wle_trans hc (hsep 0 q (by omega) (by omega) hq'))
    rw [hcount] at h
    obtain ⟨hs, hp, -, hsuf, hsep⟩ := h
    refine ⟨fun p q hpq hq => ?_, hs, hp⟩
    by_cases hp0 : p = 0
    · subst hp0
      by_cases hq0 : q = 0
      · subst hq0; exact wle_refl _
      · exact hsep 0 q (by omega) (by omega) hq
    · exact hsuf p q (by omega) hpq hq

/-- Heapsort computes the specification on every array that memory can hold. -/
theorem heapsort_eq (xs : Array UInt64) (hsize : xs.size < 2 ^ 64) :
    heapsort xs = expected xs := by
  obtain ⟨hsorted, hs, hp⟩ := heapsort_sorted_perm xs hsize
  have hpair : (heapsort xs).toList.Pairwise (· ≤ ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [Array.length_toList] at hi hj
    simp only [Array.getElem_toList]
    have := hsorted i j (Nat.le_of_lt hij) (by omega)
    rwa [getElem!_pos _ i hi, getElem!_pos _ j hj] at this
  have hms := List.pairwise_mergeSort (le := fun a b : UInt64 => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact wle_trans hab hbc)
    (fun a b => by rcases wle_total a b with h | h <;> simp [h]) xs.toList
  have hms' : (xs.toList.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) :=
    hms.imp fun h => by simpa using h
  have heq := List.Perm.eq_of_pairwise (le := (· ≤ ·))
    (fun a b _ _ hab hba => wle_antisymm hab hba) hpair hms'
    (hp.trans (List.mergeSort_perm _ _).symm)
  unfold expected
  rw [← heq, Array.toArray_toList]

end Library.Sorting.Heapsort
