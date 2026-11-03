import Library.Random.Sampling.Program
import Library.Random.Sampling.Spec
import Library.Random.Sampling.Scale
import Library.Sorting.Heapsort.Proof
import LeanExe.Dialect.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators

/-! The proof that `shuffle` satisfies `Shuffles`.  `byIndices k m a` is Algorithm P with given
indices: for `j` from `m` down to 1 it exchanges the words at `k j` and `j`.  With indices
`k j ≤ j` it permutes `a` and leaves the words after `m` in place (`byIndices_frame`), and the word
that ends at position `m` is the word that was at `k m` (`byIndices_top`).  When the words in
positions `0` to `m` are distinct, the result therefore determines the indices
(`byIndices_unique`), and every arrangement of those words has indices (`byIndices_exists`).  The
module computes `byIndices` with the indices `scale us[n - 1 - j] (j + 1)` (`shuffle_eq`), so the
word arrays that give one arrangement are those whose word `j` lies in the set of words that `scale`
maps to the arrangement's index `j`, for each `j` from 1 to `n - 1`, and their number is the
product of the sizes of those sets, which `scale_card` bounds. -/

namespace Library.Random.Sampling

open LeanExe.Dialect Library.Sorting.Heapsort

/-- Algorithm P with the indices `k`: for `j` from `m` down to 1, exchange the words at `k j` and
`j`. -/
def byIndices (k : Nat → Nat) : Nat → Array UInt64 → Array UInt64
  | 0, a => a
  | m + 1, a => byIndices k m (swap (UInt64.ofNat (k (m + 1))) (UInt64.ofNat (m + 1)) a)

/-- Indices `k j ≤ j` for `j` from 1 to `m`. -/
def Valid (k : Nat → Nat) (m : Nat) : Prop := ∀ j, 1 ≤ j → j ≤ m → k j ≤ j

/-- Distinct words in positions `0` to `m`. -/
def DistinctTo (a : Array UInt64) (m : Nat) : Prop :=
  ∀ p q, p ≤ m → q ≤ m → a[p]! = a[q]! → p = q

theorem byIndices_size (k : Nat → Nat) :
    ∀ (m : Nat) (a : Array UInt64), (byIndices k m a).size = a.size
  | 0, _ => rfl
  | m + 1, a => by rw [byIndices, byIndices_size k m, swap_size]

theorem byIndices_congr {k k' : Nat → Nat} :
    ∀ (m : Nat), (∀ j, 1 ≤ j → j ≤ m → k j = k' j) → ∀ a, byIndices k m a = byIndices k' m a
  | 0, _, _ => rfl
  | m + 1, h, a => by
    rw [byIndices, byIndices, h (m + 1) (by omega) le_rfl]
    exact byIndices_congr m (fun j h1 h2 => h j h1 (by omega)) _

/-- With indices `k j ≤ j`, `byIndices k m a` permutes `a` and keeps the words after `m`. -/
theorem byIndices_frame (k : Nat → Nat) :
    ∀ (m : Nat) (a : Array UInt64), a.size < 2 ^ 64 → m < a.size → Valid k m →
      (byIndices k m a).toList.Perm a.toList ∧ ∀ p, m < p → (byIndices k m a)[p]! = a[p]!
  | 0, _, _, _, _ => ⟨List.Perm.refl _, fun _ _ => rfl⟩
  | m + 1, a, hs, hm, hk => by
    have hkj : k (m + 1) ≤ m + 1 := hk (m + 1) (by omega) le_rfl
    have hj : (UInt64.ofNat (m + 1)).toNat = m + 1 := word_toNat (by omega)
    have hi : (UInt64.ofNat (k (m + 1))).toNat = k (m + 1) := word_toNat (by omega)
    have hbs := swap_size a (UInt64.ofNat (k (m + 1))) (UInt64.ofNat (m + 1))
    obtain ⟨hp, hf⟩ :=
      byIndices_frame k m (swap (UInt64.ofNat (k (m + 1))) (UInt64.ofNat (m + 1)) a)
      (by omega) (by omega) (fun j h1 h2 => hk j h1 (by omega))
    refine ⟨?_, fun p hp' => ?_⟩
    · rw [byIndices]; exact hp.trans (swap_perm a _ _ (by omega) (by omega))
    · rw [byIndices, hf p (by omega), swap_get a _ _ (by omega) (by omega), hj, hi,
        ite_eq_right (show p ≠ m + 1 by omega), ite_eq_right (show p ≠ k (m + 1) by omega)]

/-- The word that ends at position `m + 1` is the word that was at `k (m + 1)`. -/
theorem byIndices_top (k : Nat → Nat) (m : Nat) (a : Array UInt64) (hs : a.size < 2 ^ 64)
    (hm : m + 1 < a.size) (hk : Valid k (m + 1)) :
    (byIndices k (m + 1) a)[m + 1]! = a[k (m + 1)]! := by
  have hkj : k (m + 1) ≤ m + 1 := hk (m + 1) (by omega) le_rfl
  have hj : (UInt64.ofNat (m + 1)).toNat = m + 1 := word_toNat (by omega)
  have hi : (UInt64.ofNat (k (m + 1))).toNat = k (m + 1) := word_toNat (by omega)
  have hbs := swap_size a (UInt64.ofNat (k (m + 1))) (UInt64.ofNat (m + 1))
  obtain ⟨-, hf⟩ := byIndices_frame k m (swap (UInt64.ofNat (k (m + 1))) (UInt64.ofNat (m + 1)) a)
    (by omega) (by omega) (fun j h1 h2 => hk j h1 (by omega))
  rw [byIndices, hf (m + 1) (by omega), swap_get a _ _ (by omega) (by omega), hj, hi,
    ite_eq_left rfl]

/-- An exchange of position `i ≤ m + 1` with position `m + 1` keeps the words of positions `0` to
`m` distinct. -/
theorem distinct_swap (a : Array UInt64) (m i : Nat) (hs : a.size < 2 ^ 64) (hm : m + 1 < a.size)
    (hi : i ≤ m + 1) (hd : DistinctTo a (m + 1)) :
    DistinctTo (swap (UInt64.ofNat i) (UInt64.ofNat (m + 1)) a) m := by
  have hj : (UInt64.ofNat (m + 1)).toNat = m + 1 := word_toNat (by omega)
  have hi' : (UInt64.ofNat i).toNat = i := word_toNat (by omega)
  intro p q hp hq h
  rw [swap_get a _ _ (by omega) (by omega), swap_get a _ _ (by omega) (by omega), hj, hi',
    ite_eq_right (show p ≠ m + 1 by omega), ite_eq_right (show q ≠ m + 1 by omega)] at h
  by_cases hpi : p = i <;> by_cases hqi : q = i
  · omega
  · rw [ite_eq_left hpi, ite_eq_right hqi] at h
    have := hd _ _ le_rfl (by omega) h; omega
  · rw [ite_eq_right hpi, ite_eq_left hqi] at h
    have := hd _ _ (by omega) le_rfl h; omega
  · rw [ite_eq_right hpi, ite_eq_right hqi] at h
    exact hd _ _ (by omega) (by omega) h

/-- When the words in positions `0` to `m` are distinct, the result of `byIndices` determines the
indices. -/
theorem byIndices_unique {k k' : Nat → Nat} :
    ∀ (m : Nat) (a : Array UInt64), a.size < 2 ^ 64 → m < a.size → DistinctTo a m →
      Valid k m → Valid k' m → byIndices k m a = byIndices k' m a →
        ∀ j, 1 ≤ j → j ≤ m → k j = k' j
  | 0, _, _, _, _, _, _, _, _, h1, h2 => absurd h2 (by omega)
  | m + 1, a, hs, hm, hd, hk, hk', heq, j, h1, h2 => by
    have hkj := hk (m + 1) (by omega) le_rfl
    have hkj' := hk' (m + 1) (by omega) le_rfl
    have htop : a[k (m + 1)]! = a[k' (m + 1)]! := by
      rw [← byIndices_top k m a hs hm hk, ← byIndices_top k' m a hs hm hk', heq]
    have hkk : k (m + 1) = k' (m + 1) := hd _ _ hkj hkj' htop
    by_cases hjm : j = m + 1
    · rw [hjm]; exact hkk
    · rw [byIndices, byIndices, hkk] at heq
      have hbs := swap_size a (UInt64.ofNat (k' (m + 1))) (UInt64.ofNat (m + 1))
      exact byIndices_unique m _ (by omega) (by omega) (distinct_swap a m _ hs hm hkj' hd)
        (fun j h1 h2 => hk j h1 (by omega)) (fun j h1 h2 => hk' j h1 (by omega)) heq j h1
        (by omega)

theorem drop_eq_of_get {a b : Array UInt64} (hs : a.size = b.size) (n : Nat)
    (h : ∀ p, n ≤ p → a[p]! = b[p]!) : a.toList.drop n = b.toList.drop n := by
  apply List.ext_getElem (by simp [hs])
  intro i h1 h2
  simp only [List.length_drop, Array.length_toList] at h1 h2
  rw [List.getElem_drop, List.getElem_drop, Array.getElem_toList, Array.getElem_toList]
  have := h (n + i) (by omega)
  rwa [getElem!_pos a (n + i) (by omega), getElem!_pos b (n + i) (by omega)] at this

theorem take_add_one_get (a : Array UInt64) (n : Nat) (h : n < a.size) :
    a.toList.take (n + 1) = a.toList.take n ++ [a[n]!] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using h), Option.toList_some,
    Array.getElem_toList, getElem!_pos a n h]

/-- Every arrangement of the words in positions `0` to `m`, with the words after `m` in place,
comes from indices `k j ≤ j`. -/
theorem byIndices_exists :
    ∀ (m : Nat) (a ys : Array UInt64), a.size < 2 ^ 64 → m < a.size → ys.size = a.size →
      (ys.toList.take (m + 1)).Perm (a.toList.take (m + 1)) → (∀ p, m < p → ys[p]! = a[p]!) →
        ∃ k, Valid k m ∧ byIndices k m a = ys
  | 0, a, ys, _, hm, hys, hp, hf => by
    refine ⟨fun _ => 0, fun j h1 h2 => by omega, ?_⟩
    rw [take_add_one_get ys 0 (by omega), take_add_one_get a 0 (by omega)] at hp
    simp only [List.take_zero, List.nil_append] at hp
    have h0 := List.singleton_perm_singleton.mp hp
    show a = ys
    apply Array.ext hys.symm
    intro p hp1 hp2
    have := if hp0 : p = 0 then (by rw [hp0]; exact h0.symm) else (hf p (by omega)).symm
    rwa [getElem!_pos a p hp1, getElem!_pos ys p hp2] at this
  | m + 1, a, ys, hs, hm, hys, hp, hf => by
    have hmem : ys[m + 1]! ∈ a.toList.take (m + 2) := by
      apply hp.subset
      rw [take_add_one_get ys (m + 1) (by omega)]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    obtain ⟨p, hp1, hp2⟩ := List.getElem_of_mem hmem
    simp only [List.length_take, Array.length_toList] at hp1
    rw [List.getElem_take, Array.getElem_toList, ← getElem!_pos a p (by omega)] at hp2
    have hj : (UInt64.ofNat (m + 1)).toNat = m + 1 := word_toNat (by omega)
    have hi : (UInt64.ofNat p).toNat = p := word_toNat (by omega)
    set b := swap (UInt64.ofNat p) (UInt64.ofNat (m + 1)) a with hb
    have hbs : b.size = a.size := swap_size _ _ _
    have hbget : ∀ q, b[q]! = if q = m + 1 then a[p]! else if q = p then a[m + 1]! else a[q]! := by
      intro q; rw [hb, swap_get a _ _ (by omega) (by omega), hj, hi]
    have hdrop : b.toList.drop (m + 2) = a.toList.drop (m + 2) :=
      drop_eq_of_get hbs (m + 2) fun q hq => by
        rw [hbget q, ite_eq_right (show q ≠ m + 1 by omega), ite_eq_right (show q ≠ p by omega)]
    have htake : (b.toList.take (m + 2)).Perm (a.toList.take (m + 2)) := by
      have hperm := swap_perm a (UInt64.ofNat p) (UInt64.ofNat (m + 1)) (by omega) (by omega)
      rw [← hb, ← List.take_append_drop (m + 2) b.toList, ← List.take_append_drop (m + 2) a.toList,
        hdrop] at hperm
      exact (List.perm_append_right_iff _).mp hperm
    have hbm : b[m + 1]! = ys[m + 1]! := by rw [hbget, ite_eq_left rfl, hp2]
    have hpre : (ys.toList.take (m + 1)).Perm (b.toList.take (m + 1)) := by
      have h := hp.trans htake.symm
      rw [take_add_one_get ys (m + 1) (by omega), take_add_one_get b (m + 1) (by omega), hbm] at h
      exact (List.perm_append_right_iff _).mp h
    obtain ⟨k', hk', heq⟩ := byIndices_exists m b ys (by omega) (by omega) (by omega) hpre
      fun q hq => by
        by_cases hq1 : q = m + 1
        · rw [hq1, hbm]
        · rw [hbget q, ite_eq_right hq1, ite_eq_right (show q ≠ p by omega)]; exact hf q (by omega)
    refine ⟨fun j => if j = m + 1 then p else k' j, fun j h1 h2 => ?_, ?_⟩
    · dsimp only
      by_cases hj1 : j = m + 1
      · rw [ite_eq_left hj1]; omega
      · rw [ite_eq_right hj1]; exact hk' j h1 (by omega)
    · rw [byIndices]
      simp only [↓reduceIte]
      rw [← hb, ← heq]
      exact byIndices_congr m (fun j h1 h2 => by rw [ite_eq_right (show j ≠ m + 1 by omega)]) b

/-! ### The module's shuffle -/

/-- The index of step `j` of `shuffle us` on `n` words: `scale us[n - 1 - j] (j + 1)`. -/
def indices (us : Array UInt64) (n j : Nat) : Nat :=
  (scale us[n - 1 - j]! (UInt64.ofNat (j + 1))).toNat

theorem indices_valid (us : Array UInt64) (n m : Nat) (hm : m + 1 < 2 ^ 64) :
    Valid (indices us n) m := by
  intro j h1 h2
  have hj : (UInt64.ofNat (j + 1)).toNat = j + 1 := word_toNat (by omega)
  have := scale_lt us[n - 1 - j]! (UInt64.ofNat (j + 1)) (by omega)
  unfold indices
  omega

/-- The module's shuffle is `byIndices` with the indices of `scale`. -/
theorem shuffle_eq (us xs : Array UInt64) (hs : xs.size < 2 ^ 64) (h1 : 1 ≤ xs.size) :
    shuffle us xs = byIndices (indices us xs.size) (xs.size - 1) xs := by
  have hN : xs.size.toUInt64.toNat = xs.size := by
    simp only [Nat.toUInt64, UInt64.toNat_ofNat']; omega
  simp only [shuffle]
  by_cases hn : xs.size.toUInt64 ≤ 1
  · rw [ite_eq_left hn]
    have : xs.size = 1 := by
      have := UInt64.le_iff_toNat_le.mp hn; simp only [hN, UInt64.reduceToNat] at this; omega
    rw [this]
    rfl
  · rw [ite_eq_right hn]
    have h2 : 2 ≤ xs.size := by
      have : ¬ xs.size.toUInt64.toNat ≤ 1 := fun h =>
        hn (UInt64.le_iff_toNat_le.mpr (by simpa using h))
      omega
    have hcount : (xs.size.toUInt64 - 1).toNat = xs.size - 1 := by
      simp only [UInt64.toNat_sub, hN, UInt64.reduceToNat]; omega
    have h := loop_induction (n := xs.size.toUInt64 - 1) (init := xs)
      (f := fun t acc => swap (scale us[t.toNat]! (xs.size.toUInt64 - t))
        (xs.size.toUInt64 - 1 - t) acc)
      (P := fun t acc => acc.size = xs.size ∧
        byIndices (indices us xs.size) (xs.size - 1 - t) acc =
          byIndices (indices us xs.size) (xs.size - 1) xs)
      ⟨rfl, rfl⟩
      (by
        intro t acc ht ⟨hs', heq⟩
        rw [hcount] at ht
        have htt : (UInt64.ofNat t).toNat = t := word_toNat (by omega)
        refine ⟨by rw [swap_size, hs'], ?_⟩
        have i1 : (UInt64.ofNat t).toNat = xs.size - 1 - (xs.size - 2 - t + 1) := by
          rw [htt]; omega
        have i2 : xs.size.toUInt64 - UInt64.ofNat t = UInt64.ofNat (xs.size - 2 - t + 1 + 1) := by
          apply UInt64.toNat_inj.mp
          rw [word_toNat (by omega)]
          simp only [UInt64.toNat_sub, hN, htt]; omega
        have i3 : xs.size.toUInt64 - 1 - UInt64.ofNat t = UInt64.ofNat (xs.size - 2 - t + 1) := by
          apply UInt64.toNat_inj.mp
          rw [word_toNat (by omega)]
          simp only [UInt64.toNat_sub, hN, htt, UInt64.reduceToNat]; omega
        have i4 : UInt64.ofNat (indices us xs.size (xs.size - 2 - t + 1)) =
            scale us[xs.size - 1 - (xs.size - 2 - t + 1)]!
              (UInt64.ofNat (xs.size - 2 - t + 1 + 1)) := by
          unfold indices
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_ofNat_of_lt' (UInt64.toNat_lt _)]
        have hJ : xs.size - 1 - t = xs.size - 2 - t + 1 := by omega
        have e1 : xs.size - 1 - (t + 1) = xs.size - 2 - t := by omega
        rw [← heq, hJ, byIndices.eq_2, i1, i2, i3, ← i4, e1])
    rw [hcount, Nat.sub_self] at h
    exact h.2.symm.symm

theorem swap_map (f : UInt64 → UInt64) (a : Array UInt64) (i j : UInt64)
    (hi : i.toNat < a.size) (hj : j.toNat < a.size) :
    swap i j (a.map f) = (swap i j a).map f := by
  have hm : ∀ p, p < a.size → (a.map f)[p]! = f a[p]! := fun p hp => by
    rw [getElem!_pos _ p (by simpa using hp), Array.getElem_map, getElem!_pos a p hp]
  apply Array.ext (by simp [swap_size])
  intro q h1 h2
  have hq : q < a.size := by simpa [swap_size] using h1
  rw [← getElem!_pos _ q h1, Array.getElem_map, ← getElem!_pos _ q (by simpa [swap_size] using hq),
    swap_get _ i j (by simpa using hi) (by simpa using hj), swap_get a i j hi hj]
  by_cases hqj : q = j.toNat
  · rw [ite_eq_left hqj, ite_eq_left hqj, hm _ hi]
  · rw [ite_eq_right hqj, ite_eq_right hqj]
    by_cases hqi : q = i.toNat
    · rw [ite_eq_left hqi, ite_eq_left hqi, hm _ hj]
    · rw [ite_eq_right hqi, ite_eq_right hqi, hm _ hq]

theorem byIndices_map (f : UInt64 → UInt64) (k : Nat → Nat) :
    ∀ (m : Nat) (a : Array UInt64), a.size < 2 ^ 64 → m < a.size → Valid k m →
      byIndices k m (a.map f) = (byIndices k m a).map f
  | 0, _, _, _, _ => rfl
  | m + 1, a, hs, hm, hk => by
    have hkj := hk (m + 1) (by omega) le_rfl
    have hj : (UInt64.ofNat (m + 1)).toNat = m + 1 := word_toNat (by omega)
    have hi : (UInt64.ofNat (k (m + 1))).toNat = k (m + 1) := word_toNat (by omega)
    have hbs := swap_size a (UInt64.ofNat (k (m + 1))) (UInt64.ofNat (m + 1))
    rw [byIndices, byIndices, swap_map f a _ _ (by omega) (by omega)]
    exact byIndices_map f k m _ (by omega) (by omega) fun j h1 h2 => hk j h1 (by omega)

theorem iota_map (xs : Array UInt64) (hs : xs.size < 2 ^ 64) :
    (iota xs.size).map (fun p => xs[p.toNat]!) = xs := by
  apply Array.ext (by simp [iota])
  intro q h1 h2
  simp only [iota, Array.getElem_map, Array.getElem_ofFn]
  rw [word_toNat (by omega), getElem!_pos xs q h2]

theorem shuffle_empty (us : Array UInt64) : shuffle us #[] = #[] := by
  simp [shuffle]

/-- The results of `shuffle` are permutations. -/
theorem shuffle_perm (us xs : Array UInt64) (hs : xs.size < 2 ^ 64) :
    (shuffle us xs).toList.Perm xs.toList := by
  by_cases h0 : xs.size = 0
  · rw [Array.eq_empty_of_size_eq_zero h0, shuffle_empty]
  · rw [shuffle_eq us xs hs (by omega)]
    exact (byIndices_frame _ _ xs hs (by omega) (indices_valid us _ _ (by omega))).1

/-- The positions that `shuffle` moves do not depend on the words. -/
theorem shuffle_positions (us xs : Array UInt64) (hs : xs.size < 2 ^ 64) :
    shuffle us xs = (shuffle us (iota xs.size)).map fun p => xs[p.toNat]! := by
  have hi : (iota xs.size).size = xs.size := Array.size_ofFn
  by_cases h0 : xs.size = 0
  · have hx := Array.eq_empty_of_size_eq_zero h0
    have hio : iota xs.size = #[] := Array.eq_empty_of_size_eq_zero (by omega)
    rw [hio, shuffle_empty, hx, shuffle_empty]
    simp
  · rw [shuffle_eq us xs hs (by omega), shuffle_eq us (iota xs.size) (by omega) (by omega), hi,
      ← byIndices_map _ _ _ _ (by omega) (by omega) (indices_valid us _ _ (by omega)),
      iota_map xs hs]

/-- The word arrays that give one arrangement of distinct words are those whose word `t` lies, for
each `t`, in the set of words that `scale` maps to the arrangement's index `n - 1 - t`. -/
theorem arrays_iff (xs ys : Array UInt64) (hs : xs.size < 2 ^ 32) (hd : xs.toList.Nodup)
    (hp : ys.toList.Perm xs.toList) :
    ∃ kk : Nat → Nat, (∀ t : Fin (xs.size - 1), kk (xs.size - 1 - t.val) ≤ xs.size - 1 - t.val) ∧
      ∀ w : Fin (xs.size - 1) → UInt64, shuffle (Array.ofFn w) xs = ys ↔
        ∀ t : Fin (xs.size - 1), (scale (w t) (UInt64.ofNat (xs.size - 1 - t.val + 1))).toNat =
          kk (xs.size - 1 - t.val) := by
  have hys : ys.size = xs.size := by simpa using hp.length_eq
  by_cases h0 : xs.size = 0
  · refine ⟨fun _ => 0, fun t => absurd t.isLt (by omega),
      fun w => ⟨fun _ t => absurd t.isLt (by omega), fun _ => ?_⟩⟩
    rw [Array.eq_empty_of_size_eq_zero (show ys.size = 0 by omega)]
    apply Array.eq_empty_of_size_eq_zero
    have := (shuffle_perm (Array.ofFn w) xs (by omega)).length_eq
    simpa [h0] using this
  · obtain ⟨kk, hv, heq⟩ := byIndices_exists (xs.size - 1) xs ys (by omega) (by omega) hys
      (by
        rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp; omega)]
        exact hp)
      (fun p hp' => by rw [getElem!_neg ys p (by omega), getElem!_neg xs p (by omega)])
    have hdist : DistinctTo xs (xs.size - 1) := by
      intro p q hp1 hq1 h
      rw [getElem!_pos xs p (by omega), getElem!_pos xs q (by omega), ← Array.getElem_toList,
        ← Array.getElem_toList] at h
      exact (List.Nodup.getElem_inj_iff hd).mp h
    have hget : ∀ (w : Fin (xs.size - 1) → UInt64) (t : Fin (xs.size - 1)),
        (Array.ofFn w)[t.val]! = w t := fun w t => by
      rw [getElem!_pos _ t.val (by simp), Array.getElem_ofFn]
    refine ⟨kk, fun t => hv _ (by omega) (by omega), fun w => ?_⟩
    rw [shuffle_eq _ xs (by omega) (by omega), ← heq]
    constructor
    · intro h t
      have := byIndices_unique (xs.size - 1) xs (by omega) (by omega) hdist
        (indices_valid _ _ _ (by omega)) hv h (xs.size - 1 - t.val) (by omega) (by omega)
      rw [← this]
      unfold indices
      rw [show xs.size - 1 - (xs.size - 1 - t.val) = t.val by omega, hget]
    · intro h
      exact byIndices_congr _ (fun j h1 h2 => by
        have := h ⟨xs.size - 1 - j, by omega⟩
        unfold indices
        rw [hget w ⟨xs.size - 1 - j, by omega⟩]
        simpa [show xs.size - 1 - (xs.size - 1 - j) = j by omega] using this) xs

/-- For distinct words, every arrangement comes from between `fewest n` and `most n` word
arrays. -/
theorem shuffle_count (xs ys : Array UInt64) (hs : xs.size < 2 ^ 32) (hd : xs.toList.Nodup)
    (hp : ys.toList.Perm xs.toList) :
    fewest xs.size ≤ (arraysTo shuffle xs ys).card ∧
      (arraysTo shuffle xs ys).card ≤ most xs.size := by
  obtain ⟨kk, hkk, hmem⟩ := arrays_iff xs ys hs hd hp
  have hset : arraysTo shuffle xs ys = Fintype.piFinset fun t : Fin (xs.size - 1) =>
      Finset.univ.filter fun u : UInt64 =>
        (scale u (UInt64.ofNat (xs.size - 1 - t.val + 1))).toNat = kk (xs.size - 1 - t.val) := by
    ext w
    simp only [arraysTo, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    exact hmem w
  rw [hset, Fintype.card_piFinset,
    Fin.prod_univ_eq_prod_range (fun t => (Finset.univ.filter fun u : UInt64 =>
      (scale u (UInt64.ofNat (xs.size - 1 - t + 1))).toNat = kk (xs.size - 1 - t)).card)
      (xs.size - 1)]
  unfold fewest most
  rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range,
    ← Finset.prod_range_reflect (fun k => 2 ^ 64 / (1 + k + 1)) (xs.size - 1),
    ← Finset.prod_range_reflect (fun k => (2 ^ 64 + (1 + k)) / (1 + k + 1)) (xs.size - 1)]
  have hb : ∀ t ∈ Finset.range (xs.size - 1),
      2 ^ 64 / (xs.size - 1 - t + 1) ≤ (Finset.univ.filter fun u : UInt64 =>
        (scale u (UInt64.ofNat (xs.size - 1 - t + 1))).toNat = kk (xs.size - 1 - t)).card ∧
      (Finset.univ.filter fun u : UInt64 =>
        (scale u (UInt64.ofNat (xs.size - 1 - t + 1))).toNat = kk (xs.size - 1 - t)).card ≤
          (2 ^ 64 + (xs.size - 1 - t + 1) - 1) / (xs.size - 1 - t + 1) := fun t ht => by
    rw [Finset.mem_range] at ht
    have := hkk ⟨t, ht⟩
    exact scale_card (xs.size - 1 - t + 1) (kk (xs.size - 1 - t)) (by omega) (by omega)
      (by simp at this; omega)
  constructor
  · apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [show 1 + (xs.size - 1 - 1 - t) + 1 = xs.size - 1 - t + 1 by omega]
    exact (hb t ht).1
  · apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [show 2 ^ 64 + (1 + (xs.size - 1 - 1 - t)) = 2 ^ 64 + (xs.size - 1 - t + 1) - 1 by omega,
      show 1 + (xs.size - 1 - 1 - t) + 1 = xs.size - 1 - t + 1 by omega]
    exact (hb t ht).2

theorem swap_eq_swapIfInBounds (a : Array UInt64) (i j : UInt64) (hi : i.toNat < a.size)
    (hj : j.toNat < a.size) : swap i j a = a.swapIfInBounds i.toNat j.toNat := by
  apply Array.ext (by rw [swap_size, Array.size_swapIfInBounds])
  intro q h1 h2
  have hq : q < a.size := by simpa [swap_size] using h1
  rw [← getElem!_pos _ q h1, swap_get a i j hi hj, Array.getElem_swapIfInBounds]
  by_cases hqj : q = j.toNat <;> by_cases hqi : q = i.toNat
  · rw [ite_eq_left hqj, dite_eq_left_of_eq_true (eq_true ⟨hqi, hj⟩), getElem!_pos a _ hi]
    simp only [← hqi, ← hqj]
  · rw [ite_eq_left hqj, dite_eq_right_of_eq_false (eq_false fun h => hqi h.1),
      dite_eq_left_of_eq_true (eq_true ⟨hqj, hi⟩), getElem!_pos a _ hi]
  · rw [ite_eq_right hqj, ite_eq_left hqi, dite_eq_left_of_eq_true (eq_true ⟨hqi, hj⟩),
      getElem!_pos a _ hj]
  · rw [ite_eq_right hqj, ite_eq_right hqi, dite_eq_right_of_eq_false (eq_false fun h => hqi h.1),
      dite_eq_right_of_eq_false (eq_false fun h => hqj h.1), getElem!_pos a _ hq]

theorem byIndices_eq_algorithmP (us : Array UInt64) (n : Nat) :
    ∀ (m : Nat) (a : Array UInt64), a.size < 2 ^ 32 → m < a.size →
      byIndices (indices us n) m a = algorithmP us n m a
  | 0, _, _, _ => rfl
  | m + 1, a, hs, hm => by
    have hm2 : (UInt64.ofNat (m + 1 + 1)).toNat = m + 1 + 1 := word_toNat (by omega)
    have hk : indices us n (m + 1) = us[n - 2 - m]!.toNat * (m + 1 + 1) / 2 ^ 64 := by
      unfold indices
      rw [show n - 1 - (m + 1) = n - 2 - m by omega, scale_toNat _ _ (by omega), hm2]
    have hkl : indices us n (m + 1) ≤ m + 1 :=
      indices_valid us n (m + 1) (by omega) (m + 1) (by omega) le_rfl
    have hi : (UInt64.ofNat (indices us n (m + 1))).toNat = indices us n (m + 1) :=
      word_toNat (by omega)
    have hj : (UInt64.ofNat (m + 1)).toNat = m + 1 := word_toNat (by omega)
    rw [byIndices, algorithmP, swap_eq_swapIfInBounds a _ _ (by omega) (by omega), hi, hj, hk]
    exact byIndices_eq_algorithmP us n m _ (by simp; omega) (by simp; omega)

/-- The module's shuffle is Knuth's Algorithm P. -/
theorem shuffle_method (us xs : Array UInt64) (hs : xs.size < 2 ^ 32) :
    shuffle us xs = algorithmP us xs.size (xs.size - 1) xs := by
  by_cases h0 : xs.size = 0
  · rw [Array.eq_empty_of_size_eq_zero h0, shuffle_empty]
    rfl
  · rw [shuffle_eq us xs (by omega) (by omega)]
    exact byIndices_eq_algorithmP us _ _ xs hs (by omega)

/-- `shuffle` satisfies the specification. -/
theorem shuffle_spec : Shuffles shuffle :=
  ⟨shuffle_method, shuffle_perm, shuffle_positions, shuffle_count⟩

end Library.Random.Sampling
