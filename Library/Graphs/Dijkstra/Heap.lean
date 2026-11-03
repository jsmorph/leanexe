import Library.Graphs.Dijkstra.Program
import Library.Sorting.Heapsort.Proof
import Library.Queues.BinaryHeap.Proof
import Mathlib.Data.List.FinRange

/-! The heap of Dijkstra's algorithm: keys in `hk` and vertices in `hv`, with entry `i` the pair
`(hk[i], hv[i])`, node `i` the parent of nodes `2i + 1` and `2i + 2`, and the least key at the root.
`pairs hk hv len` lists the entries below `len`.  An exchange of two entries below `len` permutes
that list, so the sifts permute it, and `push` and `pop` state an insertion and a removal of the
root as the entries before them with one pair added or removed. -/

namespace Library.Graphs.Dijkstra

open LeanExe.Dialect
open Library.Sorting.Heapsort (swap swap_get swap_size wle_trans wle_of_lt wle_of_not_lt wle_refl)
open Library.Queues.BinaryHeap (parent_toNat sub_one_toNat)

/-- The entries below `len` as pairs of a key and a vertex. -/
def pairs (hk hv : Array UInt64) (len : Nat) : List (UInt64 × UInt64) :=
  List.ofFn fun k : Fin len => (hk[k.val]!, hv[k.val]!)

/-- The heap order on the keys below `h`: no key is below its parent's. -/
def MinHeap (hk : Array UInt64) (h : Nat) : Prop :=
  ∀ j, 0 < j → j < h → hk[(j - 1) / 2]! ≤ hk[j]!

theorem mem_pairs {hk hv : Array UInt64} {len : Nat} {e : UInt64 × UInt64} :
    e ∈ pairs hk hv len ↔ ∃ i < len, (hk[i]!, hv[i]!) = e := by
  unfold pairs
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem pairs_congr {hk hv hk' hv' : Array UInt64} {len : Nat}
    (h1 : ∀ k < len, hk'[k]! = hk[k]!) (h2 : ∀ k < len, hv'[k]! = hv[k]!) :
    pairs hk' hv' len = pairs hk hv len := by
  unfold pairs
  congr 1
  funext k
  rw [h1 k.val k.isLt, h2 k.val k.isLt]

theorem pairs_succ (hk hv : Array UInt64) (len : Nat) :
    pairs hk hv (len + 1) = pairs hk hv len ++ [(hk[len]!, hv[len]!)] := by
  unfold pairs
  rw [List.ofFn_succ_last]
  rfl

/-- An exchange of two entries below `len` permutes the entries below `len`. -/
theorem pairs_swap (hk hv : Array UInt64) (len : Nat) (i j : UInt64) (hi : i.toNat < len)
    (hj : j.toNat < len) (hks : len ≤ hk.size) (hvs : len ≤ hv.size) :
    (pairs (swap i j hk) (swap i j hv) len).Perm (pairs hk hv len) := by
  let σ : Equiv.Perm (Fin len) := Equiv.swap ⟨j.toNat, hj⟩ ⟨i.toNat, hi⟩
  have hσ : ∀ k : Fin len, (σ k).val =
      if k.val = j.toNat then i.toNat else if k.val = i.toNat then j.toNat else k.val := by
    intro k
    simp only [σ, Equiv.swap_apply_def]
    by_cases h1 : k = ⟨j.toNat, hj⟩
    · rw [ite_eq_left h1, ite_eq_left (congrArg Fin.val h1)]
    · rw [ite_eq_right h1, ite_eq_right (fun e => h1 (Fin.ext e))]
      by_cases h2 : k = ⟨i.toNat, hi⟩
      · rw [ite_eq_left h2, ite_eq_left (congrArg Fin.val h2)]
      · rw [ite_eq_right h2, ite_eq_right (fun e => h2 (Fin.ext e))]
  have e : (fun k : Fin len => ((swap i j hk)[k.val]!, (swap i j hv)[k.val]!)) =
      (fun k : Fin len => (hk[k.val]!, hv[k.val]!)) ∘ σ := by
    funext k
    simp only [Function.comp]
    rw [swap_get hk i j (by omega) (by omega), swap_get hv i j (by omega) (by omega), hσ k]
    split_ifs <;> rfl
  unfold pairs
  rw [e]
  exact Equiv.Perm.ofFn_comp_perm σ _

/-- In a heap the root holds the least key. -/
theorem root_min (hk : Array UInt64) (h : Nat) (hh : MinHeap hk h) :
    ∀ k, k < h → hk[0]! ≤ hk[k]! := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hkh
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact wle_refl _
    · exact wle_trans (ih _ (by omega) (by omega)) (hh k hpos hkh)

/-! ### The sift up -/

/-- The sift up keeps the sizes, permutes the entries below any `len` above `i`, and leaves the
entries after `i`. -/
theorem siftUp_frame (i : UInt64) (hk hv : Array UInt64) (len : Nat) (hi : i.toNat < len)
    (hks : len ≤ hk.size) (hvs : len ≤ hv.size) :
    (siftUp i hk hv).1.size = hk.size ∧ (siftUp i hk hv).2.size = hv.size ∧
      (pairs (siftUp i hk hv).1 (siftUp i hk hv).2 len).Perm (pairs hk hv len) ∧
      (∀ k, i.toNat < k → (siftUp i hk hv).1[k]! = hk[k]!) ∧
      (∀ k, i.toNat < k → (siftUp i hk hv).2[k]! = hv[k]!) := by
  rw [siftUp]
  by_cases h : 0 < i ∧ hk[i.toNat]! < hk[((i - 1) / 2).toNat]!
  · rw [ite_eq_left h]
    obtain ⟨hP, hi0⟩ := parent_toNat h.1
    obtain ⟨s1, s2, s3, s4, s5⟩ := siftUp_frame ((i - 1) / 2) (swap ((i - 1) / 2) i hk)
      (swap ((i - 1) / 2) i hv) len (by omega) (by rw [swap_size]; exact hks)
      (by rw [swap_size]; exact hvs)
    refine ⟨by rw [s1, swap_size], by rw [s2, swap_size],
      s3.trans (pairs_swap hk hv len _ _ (by omega) hi hks hvs), fun k hk' => ?_, fun k hk' => ?_⟩
    · rw [s4 k (by omega), swap_get hk _ _ (by omega) (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [s5 k (by omega), swap_get hv _ _ (by omega) (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right h]
    exact ⟨rfl, rfl, List.Perm.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
termination_by i.toNat
decreasing_by
  obtain ⟨_, _⟩ := parent_toNat h.1
  omega

/-- The invariant of an insertion: when the heap order on the keys below `m` holds at every node
except between `i` and its parent, and the keys of the children of `i` are at least the key of
the parent of `i`, the sift up makes the keys below `m` a heap. -/
theorem siftUp_spec (m : Nat) (i : UInt64) (hk hv : Array UInt64) (hm : m ≤ hk.size)
    (hi : i.toNat < m)
    (hok : ∀ j, 0 < j → j < m → j ≠ i.toNat → hk[(j - 1) / 2]! ≤ hk[j]!)
    (hbr : 0 < i.toNat → ∀ j, 0 < j → j < m → (j - 1) / 2 = i.toNat →
      hk[(i.toNat - 1) / 2]! ≤ hk[j]!) :
    MinHeap (siftUp i hk hv).1 m := by
  rw [siftUp]
  by_cases h : 0 < i ∧ hk[i.toNat]! < hk[((i - 1) / 2).toNat]!
  · rw [ite_eq_left h]
    obtain ⟨hP, hi0⟩ := parent_toNat h.1
    have hlt := h.2
    rw [hP] at hlt
    have hpa : ((i - 1) / 2).toNat < hk.size := by omega
    have hia : i.toNat < hk.size := by omega
    apply siftUp_spec m ((i - 1) / 2) (swap ((i - 1) / 2) i hk) (swap ((i - 1) / 2) i hv)
      (by rw [swap_size]; exact hm) (by omega)
    · intro j hj0 hjm hjp
      rw [swap_get hk _ _ hpa hia j, swap_get hk _ _ hpa hia ((j - 1) / 2), hP]
      rw [hP] at hjp
      by_cases h1 : j = i.toNat
      · subst h1
        have h2 : ¬ (i.toNat - 1) / 2 = i.toNat := by omega
        rw [ite_eq_left rfl, ite_eq_right h2, ite_eq_left rfl]
        exact wle_of_lt hlt
      · rw [ite_eq_right h1, ite_eq_right hjp]
        by_cases h2 : (j - 1) / 2 = i.toNat
        · rw [ite_eq_left h2]
          exact hbr hi0 j hj0 hjm h2
        · rw [ite_eq_right h2]
          by_cases h3 : (j - 1) / 2 = (i.toNat - 1) / 2
          · rw [ite_eq_left h3]
            have := hok j hj0 hjm h1
            rw [h3] at this
            exact wle_trans (wle_of_lt hlt) this
          · rw [ite_eq_right h3]
            exact hok j hj0 hjm h1
    · intro hp0 j hj0 hjm hjp
      rw [swap_get hk _ _ hpa hia j, swap_get hk _ _ hpa hia ((((i - 1) / 2).toNat - 1) / 2), hP]
      rw [hP] at hjp hp0
      have hg1 : ¬ ((i.toNat - 1) / 2 - 1) / 2 = i.toNat := by omega
      have hg2 : ¬ ((i.toNat - 1) / 2 - 1) / 2 = (i.toNat - 1) / 2 := by omega
      have hjp' : ¬ j = (i.toNat - 1) / 2 := by omega
      rw [ite_eq_right hg1, ite_eq_right hg2]
      have hpg := hok ((i.toNat - 1) / 2) hp0 (by omega) (by omega)
      by_cases h1 : j = i.toNat
      · rw [ite_eq_left h1]
        exact hpg
      · rw [ite_eq_right h1, ite_eq_right hjp']
        have := hok j hj0 hjm h1
        rw [hjp] at this
        exact wle_trans hpg this
  · rw [ite_eq_right h]
    intro j hj0 hjm
    by_cases hji : j = i.toNat
    · subst hji
      have hi0 : 0 < i := UInt64.lt_iff_toNat_lt.mpr (by simpa using hj0)
      obtain ⟨hP, -⟩ := parent_toNat hi0
      have := wle_of_not_lt fun hlt => h ⟨hi0, hlt⟩
      rwa [hP] at this
    · exact hok j hj0 hjm hji
termination_by i.toNat
decreasing_by
  obtain ⟨_, _⟩ := parent_toNat h.1
  omega

/-! ### The sift down -/

theorem child_toNat {i n : UInt64} (h : i < n / 2) :
    i.toNat < n.toNat / 2 ∧ (i + i + 1).toNat = 2 * i.toNat + 1 ∧
      (i + i + 2).toNat = 2 * i.toNat + 2 := by
  have h1 := UInt64.lt_iff_toNat_lt.mp h
  simp only [UInt64.toNat_div, UInt64.reduceToNat] at h1
  have := UInt64.toNat_lt n
  refine ⟨h1, ?_, ?_⟩ <;> simp only [UInt64.toNat_add, UInt64.reduceToNat] <;> omega

/-- The sift down keeps the sizes, permutes the entries below `n`, and leaves the entries at `n`
and beyond. -/
theorem siftDown_frame (n i : UInt64) (hk hv : Array UInt64) (hks : n.toNat ≤ hk.size)
    (hvs : n.toNat ≤ hv.size) :
    (siftDown i n hk hv).1.size = hk.size ∧ (siftDown i n hk hv).2.size = hv.size ∧
      (pairs (siftDown i n hk hv).1 (siftDown i n hk hv).2 n.toNat).Perm (pairs hk hv n.toNat) ∧
      (∀ k, n.toNat ≤ k → (siftDown i n hk hv).1[k]! = hk[k]!) ∧
      (∀ k, n.toNat ≤ k → (siftDown i n hk hv).2[k]! = hv[k]!) := by
  rw [siftDown]
  by_cases h1 : i < n / 2
  · rw [ite_eq_left h1]
    obtain ⟨hI, hc1, hc2⟩ := child_toNat h1
    have step : ∀ c : UInt64, c.toNat < n.toNat → i.toNat < c.toNat →
        (siftDown c n (swap i c hk) (swap i c hv)).1.size = hk.size ∧
        (siftDown c n (swap i c hk) (swap i c hv)).2.size = hv.size ∧
        (pairs (siftDown c n (swap i c hk) (swap i c hv)).1
          (siftDown c n (swap i c hk) (swap i c hv)).2 n.toNat).Perm (pairs hk hv n.toNat) ∧
        (∀ k, n.toNat ≤ k → (siftDown c n (swap i c hk) (swap i c hv)).1[k]! = hk[k]!) ∧
        (∀ k, n.toNat ≤ k → (siftDown c n (swap i c hk) (swap i c hv)).2[k]! = hv[k]!) := by
      intro c hc hic
      obtain ⟨s1, s2, s3, s4, s5⟩ := siftDown_frame n c (swap i c hk) (swap i c hv)
        (by rw [swap_size]; exact hks) (by rw [swap_size]; exact hvs)
      refine ⟨by rw [s1, swap_size], by rw [s2, swap_size],
        s3.trans (pairs_swap hk hv _ i c (by omega) hc hks hvs), fun k hk' => ?_, fun k hk' => ?_⟩
      · rw [s4 k hk', swap_get hk _ _ (by omega) (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
      · rw [s5 k hk', swap_get hv _ _ (by omega) (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
    by_cases h2 : i + i + 2 < n ∧ hk[(i + i + 2).toNat]! < hk[(i + i + 1).toNat]!
    · rw [ite_eq_left h2]
      have hc := UInt64.lt_iff_toNat_lt.mp h2.1
      by_cases h3 : hk[(i + i + 2).toNat]! < hk[i.toNat]!
      · rw [ite_eq_left h3]
        exact step _ hc (by omega)
      · rw [ite_eq_right h3]
        exact ⟨rfl, rfl, List.Perm.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
    · rw [ite_eq_right h2]
      by_cases h3 : hk[(i + i + 1).toNat]! < hk[i.toNat]!
      · rw [ite_eq_left h3]
        exact step _ (by omega) (by omega)
      · rw [ite_eq_right h3]
        exact ⟨rfl, rfl, List.Perm.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
  · rw [ite_eq_right h1]
    exact ⟨rfl, rfl, List.Perm.refl _, fun _ _ => rfl, fun _ _ => rfl⟩
termination_by (n - i).toNat
decreasing_by
  all_goals
    obtain ⟨_, _, _⟩ := child_toNat h1
    have := UInt64.toNat_lt n
    simp only [UInt64.toNat_sub]
    omega

/-- The invariant of a removal: when the heap order on the keys below `n` holds at every node at
or after `L` except between `i` and its children, and the keys of the children of `i` are at least
the key of the parent of `i` when `L < i`, the sift down makes the keys below `n` a heap from `L`
down. -/
theorem siftDown_spec (n : UInt64) (L : Nat) (i : UInt64) (hk hv : Array UInt64)
    (hn : n.toNat ≤ hk.size) (hL : L ≤ i.toNat)
    (hok : ∀ j, 0 < j → j < n.toNat → L ≤ (j - 1) / 2 → (j - 1) / 2 ≠ i.toNat →
      hk[(j - 1) / 2]! ≤ hk[j]!)
    (hbr : L < i.toNat → ∀ j, 0 < j → j < n.toNat → (j - 1) / 2 = i.toNat →
      hk[(i.toNat - 1) / 2]! ≤ hk[j]!) :
    ∀ j, 0 < j → j < n.toNat → L ≤ (j - 1) / 2 →
      (siftDown i n hk hv).1[(j - 1) / 2]! ≤ (siftDown i n hk hv).1[j]! := by
  rw [siftDown]
  by_cases h1 : i < n / 2
  · rw [ite_eq_left h1]
    obtain ⟨hI, hc1, hc2⟩ := child_toNat h1
    have hIa : i.toNat < hk.size := by omega
    -- the case of a move to the child `c` with the least key of the children
    have move : ∀ c : UInt64, (c.toNat = 2 * i.toNat + 1 ∨ c.toNat = 2 * i.toNat + 2) →
        c.toNat < n.toNat → hk[c.toNat]! < hk[i.toNat]! →
        (∀ j, 0 < j → j < n.toNat → (j - 1) / 2 = i.toNat → hk[c.toNat]! ≤ hk[j]!) →
        ∀ j, 0 < j → j < n.toNat → L ≤ (j - 1) / 2 →
          (siftDown c n (swap i c hk) (swap i c hv)).1[(j - 1) / 2]! ≤
            (siftDown c n (swap i c hk) (swap i c hv)).1[j]! := by
      intro c hcv hcn hlt hmin
      have hCa : c.toNat < hk.size := by omega
      have hCp : (c.toNat - 1) / 2 = i.toNat := by omega
      apply siftDown_spec n L c (swap i c hk) (swap i c hv) (by rw [swap_size]; exact hn)
        (by omega)
      · intro j hj0 hjn hjL hjm
        rw [swap_get hk _ _ hIa hCa, swap_get hk _ _ hIa hCa]
        by_cases hjC : j = c.toNat
        · subst hjC
          rw [hCp]
          simp only [show i.toNat ≠ c.toNat by omega, ite_false, ite_true]
          exact wle_of_lt hlt
        · rw [ite_eq_right hjC]
          by_cases hjI : j = i.toNat
          · rw [ite_eq_left hjI]
            have hP : (j - 1) / 2 ≠ i.toNat := by omega
            have hP' : (j - 1) / 2 ≠ c.toNat := by omega
            rw [ite_eq_right hP', ite_eq_right hP]
            have := hbr (by omega) c.toNat (by omega) hcn hCp
            rw [hjI] at hP ⊢
            exact this
          · rw [ite_eq_right hjI]
            by_cases hP : (j - 1) / 2 = i.toNat
            · rw [ite_eq_right (show (j - 1) / 2 ≠ c.toNat by omega), ite_eq_left hP]
              exact hmin j hj0 hjn hP
            · rw [ite_eq_right hjm, ite_eq_right hP]
              exact hok j hj0 hjn hjL hP
      · intro _ j hj0 hjn hjp
        rw [swap_get hk _ _ hIa hCa, swap_get hk _ _ hIa hCa, hCp]
        have h3 : j ≠ c.toNat := by omega
        have h4 : j ≠ i.toNat := by omega
        have h5 : i.toNat ≠ c.toNat := by omega
        simp only [h3, h4, h5, ite_false, ite_true]
        have := hok j hj0 hjn (by omega) (by omega)
        rwa [hjp] at this
    -- the case of no move
    have stay : (∀ j, 0 < j → j < n.toNat → (j - 1) / 2 = i.toNat → hk[i.toNat]! ≤ hk[j]!) →
        ∀ j, 0 < j → j < n.toNat → L ≤ (j - 1) / 2 → hk[(j - 1) / 2]! ≤ hk[j]! := by
      intro hle j hj0 hjn hjL
      by_cases hP : (j - 1) / 2 = i.toNat
      · rw [hP]; exact hle j hj0 hjn hP
      · exact hok j hj0 hjn hjL hP
    by_cases h2 : i + i + 2 < n ∧ hk[(i + i + 2).toNat]! < hk[(i + i + 1).toNat]!
    · rw [ite_eq_left h2]
      have hc := UInt64.lt_iff_toNat_lt.mp h2.1
      have hmin : ∀ j, 0 < j → j < n.toNat → (j - 1) / 2 = i.toNat →
          hk[(i + i + 2).toNat]! ≤ hk[j]! := by
        intro j _ _ hjp
        rcases (show j = 2 * i.toNat + 1 ∨ j = 2 * i.toNat + 2 by omega) with rfl | rfl
        · rw [← hc1]; exact wle_of_lt h2.2
        · rw [← hc2]; exact wle_refl _
      by_cases h3 : hk[(i + i + 2).toNat]! < hk[i.toNat]!
      · rw [ite_eq_left h3]
        exact move _ (.inr hc2) hc h3 hmin
      · rw [ite_eq_right h3]
        exact stay fun j hj0 hjn hjp => wle_trans (wle_of_not_lt h3) (hmin j hj0 hjn hjp)
    · rw [ite_eq_right h2]
      have hmin : ∀ j, 0 < j → j < n.toNat → (j - 1) / 2 = i.toNat →
          hk[(i + i + 1).toNat]! ≤ hk[j]! := by
        intro j _ hjn hjp
        rcases (show j = 2 * i.toNat + 1 ∨ j = 2 * i.toNat + 2 by omega) with rfl | rfl
        · rw [← hc1]; exact wle_refl _
        · rw [← hc2]
          refine wle_of_not_lt fun hlt => h2 ⟨UInt64.lt_iff_toNat_lt.mpr (by omega), hlt⟩
      by_cases h3 : hk[(i + i + 1).toNat]! < hk[i.toNat]!
      · rw [ite_eq_left h3]
        exact move _ (.inl hc1) (by omega) h3 hmin
      · rw [ite_eq_right h3]
        exact stay fun j hj0 hjn hjp => wle_trans (wle_of_not_lt h3) (hmin j hj0 hjn hjp)
  · rw [ite_eq_right h1]
    intro j hj0 hjn hjL
    by_cases hP : (j - 1) / 2 = i.toNat
    · exfalso
      exact h1 (UInt64.lt_iff_toNat_lt.mpr (by
        simp only [UInt64.toNat_div, UInt64.reduceToNat]; omega))
    · exact hok j hj0 hjn hjL hP
termination_by (n - i).toNat
decreasing_by
  all_goals
    obtain ⟨_, _, _⟩ := child_toNat h1
    have := UInt64.toNat_lt n
    simp only [UInt64.toNat_sub]
    omega

/-! ### Insertion and removal -/

/-- An insertion: the pair `(key, v)` at position `h`, then the sift up, makes the keys below
`h + 1` a heap whose entries are those below `h` with `(key, v)` added. -/
theorem push_spec (hk hv : Array UInt64) (h key v : UInt64) (hh : MinHeap hk h.toNat)
    (hks : h.toNat < hk.size) (hvs : h.toNat < hv.size) :
    (siftUp h (hk.set! h.toNat key) (hv.set! h.toNat v)).1.size = hk.size ∧
      (siftUp h (hk.set! h.toNat key) (hv.set! h.toNat v)).2.size = hv.size ∧
      MinHeap (siftUp h (hk.set! h.toNat key) (hv.set! h.toNat v)).1 (h.toNat + 1) ∧
      (pairs (siftUp h (hk.set! h.toNat key) (hv.set! h.toNat v)).1
        (siftUp h (hk.set! h.toNat key) (hv.set! h.toNat v)).2 (h.toNat + 1)).Perm
        (pairs hk hv h.toNat ++ [(key, v)]) := by
  have hks1 : (hk.set! h.toNat key).size = hk.size := Array.size_set! ..
  have hvs1 : (hv.set! h.toNat v).size = hv.size := Array.size_set! ..
  obtain ⟨f1, f2, f3, -, -⟩ := siftUp_frame h (hk.set! h.toNat key) (hv.set! h.toNat v)
    (h.toNat + 1) (by omega) (by rw [hks1]; omega) (by rw [hvs1]; omega)
  refine ⟨f1.trans hks1, f2.trans hvs1, ?_, ?_⟩
  · apply siftUp_spec (h.toNat + 1) h _ _ (by rw [hks1]; omega) (by omega)
    · intro j hj0 hjm hjh
      rw [get_set hk _ _ j hks, get_set hk _ _ _ hks, ite_eq_right hjh,
        ite_eq_right (show (j - 1) / 2 ≠ h.toNat by omega)]
      exact hh j hj0 (by omega)
    · intro _ j hj0 hjm hjp
      omega
  · refine f3.trans ?_
    rw [pairs_succ, pairs_congr (hk := hk) (hv := hv) (fun k hk' => by
        rw [get_set hk _ _ k hks, ite_eq_right (by omega)])
      (fun k hk' => by rw [get_set hv _ _ k hvs, ite_eq_right (by omega)]),
      get_set hk _ _ _ hks, get_set hv _ _ _ hvs, ite_eq_left rfl, ite_eq_left rfl]

/-- A removal: the last entry moves to the root, and the sift down makes the keys below `h - 1` a
heap whose entries, with the old root, are the entries below `h`. -/
theorem pop_spec (hk hv : Array UInt64) (h : UInt64) (hh : MinHeap hk h.toNat) (h0 : 0 < h.toNat)
    (hks : h.toNat ≤ hk.size) (hvs : h.toNat ≤ hv.size) :
    (siftDown 0 (h - 1) (hk.set! (0 : UInt64).toNat hk[(h - 1).toNat]!)
        (hv.set! (0 : UInt64).toNat hv[(h - 1).toNat]!)).1.size = hk.size ∧
      (siftDown 0 (h - 1) (hk.set! (0 : UInt64).toNat hk[(h - 1).toNat]!)
        (hv.set! (0 : UInt64).toNat hv[(h - 1).toNat]!)).2.size = hv.size ∧
      MinHeap (siftDown 0 (h - 1) (hk.set! (0 : UInt64).toNat hk[(h - 1).toNat]!)
        (hv.set! (0 : UInt64).toNat hv[(h - 1).toNat]!)).1 (h.toNat - 1) ∧
      (pairs hk hv h.toNat).Perm ((hk[0]!, hv[0]!) ::
        pairs (siftDown 0 (h - 1) (hk.set! (0 : UInt64).toNat hk[(h - 1).toNat]!)
            (hv.set! (0 : UInt64).toNat hv[(h - 1).toNat]!)).1
          (siftDown 0 (h - 1) (hk.set! (0 : UInt64).toNat hk[(h - 1).toNat]!)
            (hv.set! (0 : UInt64).toNat hv[(h - 1).toNat]!)).2 (h.toNat - 1)) := by
  have hm1 := sub_one_toNat h0
  have hz : (0 : UInt64).toNat = 0 := rfl
  rw [hz, hm1]
  have hks1 : (hk.set! 0 hk[h.toNat - 1]!).size = hk.size := Array.size_set! ..
  have hvs1 : (hv.set! 0 hv[h.toNat - 1]!).size = hv.size := Array.size_set! ..
  obtain ⟨f1, f2, f3, -, -⟩ := siftDown_frame (h - 1) 0 (hk.set! 0 hk[h.toNat - 1]!)
    (hv.set! 0 hv[h.toNat - 1]!) (by rw [hks1, hm1]; omega) (by rw [hvs1, hm1]; omega)
  rw [hm1] at f3
  refine ⟨f1.trans hks1, f2.trans hvs1, ?_, ?_⟩
  · have := siftDown_spec (h - 1) 0 0 (hk.set! 0 hk[h.toNat - 1]!) (hv.set! 0 hv[h.toNat - 1]!)
      (by rw [hks1, hm1]; omega) (Nat.zero_le _) (fun j hj0 hjn _ hjp => by
        rw [hm1] at hjn
        simp only [UInt64.reduceToNat] at hjp
        rw [get_set hk 0 _ j (by omega), get_set hk 0 _ ((j - 1) / 2) (by omega),
          ite_eq_right (show j ≠ 0 by omega), ite_eq_right hjp]
        exact hh j hj0 (by omega)) (fun h' => absurd h' (by simp))
    rw [hm1] at this
    exact fun j hj0 hjn => this j hj0 hjn (Nat.zero_le _)
  · have hsw := pairs_swap hk hv h.toNat 0 (h - 1) (by simp; omega) (by rw [hm1]; omega) hks hvs
    have hsplit : pairs (swap 0 (h - 1) hk) (swap 0 (h - 1) hv) (h.toNat - 1 + 1) =
        pairs (hk.set! 0 hk[h.toNat - 1]!) (hv.set! 0 hv[h.toNat - 1]!) (h.toNat - 1) ++
          [(hk[0]!, hv[0]!)] := by
      rw [pairs_succ]
      congr 1
      · apply pairs_congr
        · intro k hk'
          rw [swap_get hk 0 (h - 1) (by simp; omega) (by rw [hm1]; omega), hm1,
            get_set hk 0 _ k (by omega)]
          by_cases hk0 : k = 0
          · subst hk0
            simp [show (0 : Nat) ≠ h.toNat - 1 by omega]
          · simp [hk0, show k ≠ h.toNat - 1 by omega]
        · intro k hk'
          rw [swap_get hv 0 (h - 1) (by simp; omega) (by rw [hm1]; omega), hm1,
            get_set hv 0 _ k (by omega)]
          by_cases hk0 : k = 0
          · subst hk0
            simp [show (0 : Nat) ≠ h.toNat - 1 by omega]
          · simp [hk0, show k ≠ h.toNat - 1 by omega]
      · rw [swap_get hk 0 (h - 1) (by simp; omega) (by rw [hm1]; omega),
          swap_get hv 0 (h - 1) (by simp; omega) (by rw [hm1]; omega), hm1, ite_eq_left rfl,
          ite_eq_left rfl]
        rfl
    rw [Nat.sub_add_cancel (show 1 ≤ h.toNat by omega)] at hsplit
    rw [hsplit] at hsw
    exact hsw.symm.trans ((List.perm_append_singleton _ _).trans (f3.symm.cons _))

end Library.Graphs.Dijkstra
